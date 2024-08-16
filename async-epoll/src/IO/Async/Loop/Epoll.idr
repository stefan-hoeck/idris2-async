module IO.Async.Loop.Epoll

import public Data.Nat
import Data.Queue
import Data.SnocList
import Data.SortedMap as SM
import Data.Vect

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref
import IO.Async.Internal.Token

import public IO.Async
import public IO.Async.Loop
import public IO.Async.Loop.SignalH
import public IO.Async.Loop.TimerH

import System
import System.Linux.Epoll
import System.Linux.EventFD
import System.Linux.SignalFD
import System.Linux.TimerFD

%default total

trace : Lazy String -> PrimIO ()
trace s = toPrim (putStrLn s)
-- trace s = MkIORes ()


||| An event handler for file descriptor events
public export
record FileHandle where
  constructor FH
  ||| What to do in case of an event
  actOn     : Events -> PrimIO ()

  ||| If the event should be observed once only
  oneShot   : Bool

  ||| If the file descriptor should automatically be closed after
  ||| handling the event
  autoClose : Bool

||| State of a single thread of a multi-threaded epoll event loop.
export
record EpollST where
  constructor EST
  nr       : Nat
  lock     : Mutex
  spwn     : EventFD
  epoll    : EpollFD
  alive    : Ref Alive
  queue    : Ref (Queue $ PrimIO ())
  outer    : Ref (Queue $ Package EpollST)
  handles  : Ref (SortedMap Bits32 FileHandle)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

submitWork : EpollST -> PrimIO () -> PrimIO ()
submitWork s a w = enq s.queue a w

indices : (n : Nat) -> Vect n Nat
indices 0     = []
indices (S k) = k :: indices k

removeFile : EpollST -> Bits32 -> (autoClose : Bool) -> PrimIO ()
removeFile s f cl w =
  let MkIORes _ w := epollDel s.epoll f w
      MkIORes _ w := modRef s.handles (delete f) w
   in primWhen cl (close f) w

export
addHandle :
     {auto fd : FileDesc a}
  -> (file : a)
  -> Events
  -> Epoll.Flags
  -> FileHandle
  -> EpollST
  -> PrimIO (PrimIO ())
addHandle file es fs fh s w =
  let fd          := fileDesc file
      MkIORes _ w := epollAdd s.epoll fd es fs w
      MkIORes _ w := modRef s.handles (insert fd fh) w
   in MkIORes (removeFile s fd fh.autoClose) w

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export
TimerH EpollST where
  primWaitTill s cl f w =
    let MkIORes now w := toPrim (clockTime Monotonic) w
     in case now >= cl of
          True  => let MkIORes _ w := f w in MkIORes primDummy w
          False =>
            let MkIORes ft  w := timerCreate MONOTONIC neutral w
                MkIORes _   w := setTime ft (timeDifference cl now) w
             in addHandle ft EPOLLIN EPOLLET (FH (const f) True True) s w

export
SignalH EpollST where
  primOnSignal s sig f w =
    let MkIORes _   w := blockSignals [sig] w
        MkIORes fs  w := signalCreate [sig] neutral w
     in addHandle fs EPOLLIN EPOLLET (FH (const f) True True) s w

--------------------------------------------------------------------------------
-- Loop Implementation
--------------------------------------------------------------------------------

FETCH_INTERVAL : Nat
FETCH_INTERVAL = 16

-- drain : EpollST -> PrimIO Bool
-- drain s w = let MkIORes _ w := readEv s.spwn w in MkIORes False w

poll : EpollST -> Int32 -> PrimIO ()
poll s t w =
  let MkIORes r w := epollWait s.epoll t w
   in case r of
        NoEv   => MkIORes () w
        Ev f e =>
          let MkIORes m w := readRef s.handles w
              Just h      := lookup f m | Nothing => MkIORes () w
              MkIORes _ w := primWhen h.oneShot (removeFile s f h.autoClose) w
           in h.actOn e w
        Err x  => trace "Polling error: \{x}" w

pkg : EpollST -> PrimIO Bool
pkg s =
  withMutex s.lock $ \w =>
    let MkIORes (Just p) w := deq s.outer w
          | MkIORes _ w =>
              let MkIORes (Left EAGAIN) w := readEv s.spwn w
                    | MkIORes r w =>
                        let MkIORes _ w := trace "Error when reading spawn file: got \{show r}" w
                         in MkIORes False w
               in MkIORes False w
        MkIORes _ w        := writeRef p.env s w
        MkIORes _ w        := enq s.queue p.act w
        MkIORes (Right 1) w := readEv s.spwn w
          | MkIORes r w =>
              let MkIORes _ w := trace "Error when reading spawn file: got \{show r}" w
               in MkIORes True w
     in MkIORes True w

-- make sure we have nothing to do and have not been stopped, and
-- if that's the case, go to sleep
rest : EpollST -> PrimIO Work
rest s w =
  let MkIORes False w := pkg s w | MkIORes _ w => noWork w
      MkIORes Run   w := readRef s.alive w | MkIORes _ w => done w
      MkIORes _     w := poll s 1 w
      MkIORes Run   w := readRef s.alive w | MkIORes _ w => done w
      MkIORes _     w := pkg s w
   in noWork w

covering
run : EpollST -> Nat -> PrimIO ()
run s 0  w =
  let MkIORes _ w := poll s 0 w
      MkIORes _ w := pkg s w
   in run s FETCH_INTERVAL w

run s (S k) w =
  let MkIORes mp w := deq s.queue w
   in case mp of
        Nothing =>
          let MkIORes (W _) w := rest s w | MkIORes _ w => MkIORes () w
           in run s k w
        Just p => let MkIORes _ w := p w in run s k w

-- initialize the state of a worker thread.
covering
epollST :
     Mutex
  -> (cncl,spwn : EventFD)
  -> Ref (Queue $ Package EpollST)
  -> Ref Alive
  -> Nat
  -> IO EpollST
epollST lock cncl spwn queue alive n = do
  Right efd <- epollCreate | Left err => die "Epoll error: \{err}"
  tasks     <- fromPrim (newRef empty)
  handles   <- fromPrim (newRef empty)
  let s := EST n lock spwn efd alive tasks queue handles
  _         <- fromPrim $ epollAdd efd spwn EPOLLIN EPOLLEXCLUSIVE
  _         <- fromPrim $ epollAdd efd cncl EPOLLIN neutral
  pure s

export
record EpollPool where
  constructor EP
  ids   : List ThreadID
  lock  : Mutex
  spwn  : EventFD
  cncl  : EventFD
  alive : Ref Alive
  queue : Ref (Queue $ Package EpollST)

||| Sets the `stopped` flag of all worker threads and awaits
||| their termination.
export
stop : EpollPool -> IO ()
stop tp = do
  primIO $ withMutex tp.lock $ \w =>
    let MkIORes _ w := writeRef tp.alive Stop w
     in writeEv tp.cncl (cast $ length tp.ids) w
  traverse_ (\x => threadWait x) tp.ids
  fromPrim $ close tp.spwn
  fromPrim $ close tp.cncl

export
submit : EpollPool -> Package EpollST -> PrimIO ()
submit tp p =
  withMutex tp.lock $ \w =>
    let MkIORes _ w := modRef tp.queue (`enqueue` p) w
     in writeEv tp.spwn 1 w


export covering
epollLoop : (n : Nat) -> (0 p : IsSucc n) => IO (EventLoop EpollST, IO ())
epollLoop (S k) = do
  lock  <- fromPrim $ mkMutex
  spwn  <- fromPrim $ eventfd 0 (EFD_SEMAPHORE <+> EFD_NONBLOCK)
  cncl  <- fromPrim $ eventfd 0 neutral
  queue <- fromPrim $ newRef empty
  alive <- primIO (newRef Run)
  sts   <- traverse (epollST lock cncl spwn queue alive) (indices $ S k)
  ts    <- for sts $ \x => fork (fromPrim $ run x 0)
  putStrLn "Starting epoll loop on \{show $ S k} threads. Spawn FD: \{show $ fileDesc spwn}, cancel FD: \{show $ fileDesc cncl}"
  let tp := EP (toList ts) lock spwn cncl alive queue
  pure (EL (submit tp) submitWork (head sts), stop tp)

export covering
app : (n : Nat) -> {auto 0 p : IsSucc n} -> Async EpollST [] () -> IO ()
app n act = do
  (el,close) <- epollLoop n
  m  <- primIO mkMutex
  c  <- primIO makeCondition
  tg <- newTokenGen
  runAsyncWith 1024 el act (\_ => putStrLn "Done. Shutting down" >> fromPrim (conditionBroadcast c))
  primIO $ acqMutex m
  primIO $ conditionWait c m
  close
  usleep 100
