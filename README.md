# An asynchronous runtime for Idris2

This is a library for running cancelable asynchronous computations
with proper error handling in Idris2. Depending on the backend you
use, this also offers true parallelism, that is, computations running in
parallel on multicore systems. It was strongly inspired by the
[cats-effect](https://typelevel.org/cats-effect/) library written in
Scala, although it is by far not as battle hardened as its antetype.

This is a literate Idris source file, so you can compile and run it.
It is recommended to use [pack](https://github.com/stefan-hoeck/idris2-pack)
for building and running the example applications:

```sh
pack install-app async-docs
async-docs [args]
```

Before we start, let's import a couple of modules:

```idris
module README

import Data.DPair
import Data.List
import IO.Async.Loop.Poller
import IO.Async.Loop.Posix
import IO.Async.Signal
import IO.Async.Posix
import System
import System.Posix.File

%default total
```

## Introducing the `Async` Monad

This library provides a new data type `Async e es a` for describing
cancelable, asynchronous computations that can fail with one of the errors
listed in `es` and yield a result of type `a` if all goes well. Asynchronous
computations need to be run on an event loop, which provides an environment
of type `e`. This environment can make additional capabilities available.
For instance, it can allow us to register timers, signal handlers, or
provide non-blocking I/O for reading data streams such as pipes or sockets.

Before we look at a first example, we need to get our terminology straight.

* synchronous: Synchronous computations are typically defined via
  `pure` or `liftIO`: They are the typical sequential effects we know
  from the `IO` monad.
* asynchronous: Asynchronous computations are defined using
  `primAsync` and produce their result by invoking
  a callback. Especially in JavaScript, many methods work asynchronously
  and will invoke a callback function once they have their result ready.
  While this allows us to continue with other work until the desired
  result is ready, working with (sometimes deeply nested) callbacks
  can be cumbersome and verbose. One advantage of `Async` is that it
  unifies synchronous and asynchronous effects in a single data
  type allowing us to conveniently mix and sequence them via the
  bind operator.
* concurrency: Concurrent actions are independent in their control flow.
  This is the opposite of "sequential" in the sense that concurrent
  effects can occur in arbitrary order, since they are processed
  independently.
* parallelism: Two computations run *in parallel*, when they are
  processed by more than one physical core or processor. Parallelism
  always implies concurrency, but concurrency not necessarily implies
  parallelism. For instance, on JavaScript - which is single-threaded -
  computations can be run concurrently but obviously not in parallel.
* fiber: A lightweight computational thread (sometimes also called a *green thread*)
  on which effectful computations run sequentially. Unlike operating
  system threads, fibers are lightweight and not a scarce resource.
  Whenever we want to run several effectful computations concurrently,
  we spawn a new fiber for each of them.
* fiber blocking: A fiber is said to be *blocked*, if
  its sequence of computations has (possibly temporarily) come to a halt
  without actually blocking the operating system thread it runs on.
  In a perfect world, we always want to get fiber blocking, that is, we try
  to avoid blocking one of the precious operating system threads at
  all cost. We therefore need to be careful when wrapping arbitrary
  I/O calls in the `Async` monad. For instance, a call to `Prelude.getLine`
  will indefinitely block the current thread until it can read a line
  of text from standard input. On the other hand, a call to
  `IO.Async.Posix.readnb Stdin` will block the current *fiber*
  until a chunk of bytes can be read from standard input *without*
  blocking the thread the fiber runs on. This means, that on a
  thread pool with four operating system threads we can at most
  use four blocking I/O calls before all threads are blocked and the
  application comes to a halt. With non-blocking I/O such as `readnb`,
  we can literally wait on thousands of file descriptors at the same time,
  and the application will still be running and ready for more.
  The same goes for calls to `System.sleep`, which will block the
  current operating system thread for the given number of seconds, while
  a call to `IO.Async.Util.sleep` will block the current *fiber*
  for the given duration.

In order to demonstrate some of this library's capabilities,
we define two countdowns: One for counting down seconds,
the other counting down milliseconds (in 100 ms steps):

```idris
countSeconds : TimerH e => Nat -> Async e [Errno] ()
countSeconds 0     = stdoutLn "Second counter done."
countSeconds (S k) = do
  stdoutLn "\{show $ S k} s left"
  sleep 1.s
  countSeconds k

countMillis : TimerH e => Nat -> Async e [Errno] ()
countMillis 0     = stdoutLn "Millisecond counter done."
countMillis (S k) = do
  stdoutLn "\{show $ S k * 100} ms left"
  sleep 100.ms
  countMillis k
```

This is very straight forward: On every recursive step, we *sleep*
for a short amount of time, before continuing the computation. Since
these are `do` blocks, computations are connected via *bind* `(>>=)`,
and this means strict sequencing of computations. Bind will not and
cannot change the order in which the computations are being run,
and it will only proceed to the next computation
when the current one has finished with a result.

Note, however, that in the examples above there is not blocking of
operating system threads, even though we call `sleep`. I will explain this in
greater detail later when we talk about `Fiber`s, but for now suffice
to say that the `sleep` used above (from module `IO.Async.Util`)
is more powerful than `System.sleep` from the base library although
they semantically do the same thing: They stop a sequence of computations
for a predefined amount of time. Note also, that we need the event loop
used to run our computations to provide the `TimerH` capability.

Let's try and run the two countdowns sequentially:

```idris
countSequentially : Async Poll [Errno] ()
countSequentially = do
  stdoutLn "Sequential countdown:"
  countSeconds 2
  countMillis 10
```

You can try this example by running `main` with the `"seq"` command-line
argument:

```sh
> async-docs seq
Sequential countdown:
2 s left
1 s left
Second counter done.
1000 ms left
900 ms left
800 ms left
700 ms left
600 ms left
500 ms left
400 ms left
300 ms left
200 ms left
100 ms left
Millisecond counter done.
```

And behold!, the two countdowns will be run one after the other as we would
expect.

Assume now, that the two countdowns are arbitrary long-running computations.
Why should we wait for the first to finish before starting the second when
they are completely unrelated? Let's try and run them concurrently as we would
with `Prelude.fork`. The primitive to do this is called `start`, and like
`fork`, it returns a value that we can use to wait for the computation
to finish using `wait`. Here's the code:


```idris
countParallel : TimerH e => Async e [Errno] ()
countParallel = do
  stdoutLn "Concurrent countdown"
  f1 <- start $ countSeconds 2
  f2 <- start $ countMillis 10
  wait f1
  wait f2
```

If you try this example by running `main` with the `"par"` argument, you will
notice that the messages from the two countdowns are now interleaved giving
at least the illusion of concurrency. However, just like `sleep` and unlike
`Prelude.threadWait`, `wait` will not block an operating
system thread, and other computations could still run concurrently on the
current thread.

```sh
> async-docs par
Concurrent countdown
1000 ms left
2 s left
900 ms left
800 ms left
700 ms left
600 ms left
500 ms left
400 ms left
300 ms left
200 ms left
100 ms left
Millisecond counter done.
1 s left
Second counter done.
```

Since running several computations and collecting their results
concurrently is such a common thing to do, there is also utility
`par`, which takes a heterogeneous list of computations and
stores their results again in a heterogeneous list (use `"par2"` as the
command-line argument to run the next example):

```idris
countParallel2 : TimerH e =>  Async e [Errno] ()
countParallel2 = ignore $ par [ countSeconds 2, countMillis 10 ]
```

Another thing to do with two or more potentially long-running
computations is to run them concurrently until one of them
terminates. This would allow us to - for instance - run a
long-running computation until a timeout fires, in which case
we might want to end with an error. We will look at that example
later on. For now, let's just run our countdowns concurrently
until the faster of the two terminates. To spice this up a bit,
we also add a signal handler so we can abort the program by
entering `Ctrl-c` at the terminal:

```idris
covering
raceParallel : TimerH e => SignalH e => Async e [Errno] ()
raceParallel = do
  stdoutLn "Racing countdowns"
  ignore $ race
    [ countSeconds 10000
    , countMillis 200
    , onSignal SIGINT (stdoutLn "\nInterrupted by SIGINT")
    ]
```

Running this with the `"race"` command-line argument gives the
following output, unless it is interrupted by `Ctrl-c`:

```sh
> pack run async-docs race
Racing countdowns
10000 s left
20000 ms left
19900 ms left
...
100 ms left
9980 s left
Millisecond counter done.
```

As you can see, after the millisecond counter finishes, the seconds counter
is canceled immediately and the application terminates even though the seconds
counter had still a long time to go!

## Fibers

Just like in cats-effect, a `Fiber` is the main abstraction this library offers.
It is sometimes also called a *green thread* because just like an operating
system thread it describes a chain of computations running sequentially. However,
unlike operating system threads, which are an extremely scarce resource,
fibers are very lightweight. Don't believe me? Let's create an application
computing a huge number of Fibonacci numbers concurrently:

```idris
fibo : Nat -> Nat
fibo 0         = 1
fibo 1         = 1
fibo (S $ S k) = fibo k + fibo (S k)

sumFibos : Nat -> Nat -> Async e es ()
sumFibos nr fib = do
  vs <- parTraverse (\n => lazy (fibo n)) (replicate nr fib)
  printLn (maybe 0 sum vs)
```

You can try this by running the example application like so:

```sh
> async-docs fibo 1000 20
10946000
```

The first numeric argument is the number of concurrent computations to
run (and thus, the number of fibers that will be created), the second
tells the application what Fibonacci number to compute. If you feel
adventurous, try increasing the number of fibers to one million.
This will undoubtedly consume quite a bit of memory and take up
to a minute to terminate, but terminate it will. It would be
unthinkable to create that number of operating system threads!

However, the example above is not a typical use case for this library.
Since these are long running CPU computations, they inadvertently block
the threads used internally in our event loop. Here's another example
with a more typical use case: Running a large number of timers in
parallel. In a real application, these could be fibers trying to
read from or write to different sockets. We do not want any system
thread to be blocked in such a scenario since we are just waiting for
an event to occur. As such, we want to be able to run *a lot* of these
computations in parallel:

```idris
restFiber : TimerH e => Integer -> Async e [Errno] ()
restFiber n = do
  sleep 100.ms
  when ((n `mod` 100) == 0) (stdoutLn "fiber \{show n} done")

sleepMany : TimerH e => Nat -> Async e [Errno] ()
sleepMany 0     = pure ()
sleepMany (S k) = ignore $ parTraverse restFiber [0 .. cast k]
```

You can try this by running the application like so:

```sh
> async-docs sleep 200
fiber 0 done
...
```

You will note that even in case of many fibers running in parallel, the running
time of the whole application only slightly increases due to the inner
scheduling of fibers which is not completely free.

### But what about parallelism?

The ability to create an almost unlimited amount of concurrently
running computations is a big advantage of fibers. But what about
true parallelism? Can the computations actually be run on several
physical cores?

The answer to that depends on the backend we use. This example
application is supposed to be run on one of Idris's Scheme backends,
and can thus make use of more than one physical core. The core function for
running an `Async` computation is `IO.Async.Type.runAsyncWith`, which
takes an `EventLoop e` as its first argument. Typically an implementation
of `EventLoop e` comes with its own convenience functions for
starting the loop and running computations.

An `EventLoop`'s main functionality is to provide function
`spawn`, which allows us to enqueue an arbitrary `IO1` action (this is
like `PrimIO` but comes from the *ref1* library) that
will then be processed by the execution context. One implementation
of this type is provided in module `IO.Async.Loop.ThreadPool`, which
uses a fixed-size pool of operating system
threads to process the enqueued `IO` actions. If the number of
threads is greater than one, we get true parallelism when processing
more than one fiber at a time.

Here is a way of visualizing this behavior. We again compute Fibonacci
numbers, but this time we make sure that the numbers we compute are
large enough to take hundreds of milliseconds at the least. In addition,
we print ever result to get an idea of the runtime behavior:

```idris
sumVisFibos : Nat -> Nat -> Async Poll [Errno] ()
sumVisFibos nr fib = do
  vs <- parTraverse visFibo (replicate nr fib)
  printLn (maybe 0 sum vs)

  where
    visFibo : Nat -> Async Poll [Errno] Nat
    visFibo n = lazy (fibo n) >>= \x => printLn x $> x
```

Run this with the `"vis_fibo"` command-line argument, but before doing
this you might want to change the number of operating system threads
to use by setting environment variable `$IDRIS2_ASYNC_THREADS` (the
default is to use four threads):

```sh
export IDRIS2_ASYNC_THREADS="2"
async-docs vis_fibo 10 42
```

With the arguments shown above, you will probably note
that the results are always printed pairwise in quick
succession before the app is again silent for a couple of
seconds. By changing the number of threads you might get
larger blocks of quickly printed results, an indicator that
several computations are indeed processed in parallel before
the next bunch of computations start.

## The `main` function

This final sections only shows the `main` functions and a few utilities
used to run the examples in this introduction. Currently, the event
loop from `IO.Async.Loop.ThreadPool` is used to run this. This makes use of
`epoll` internally, which is only available under Linux.

```idris
covering
act : List String -> Async Poll [Errno] ()
act ("par"   :: _)    = countParallel
act ("par2"  :: _)    = countParallel2
act ("race"  :: _)    = raceParallel
act ["fibo",x,y]      = sumFibos (cast x) (cast y)
act ("fibo" :: _)     = sumFibos 1000 30
act ["vis_fibo",x,y]  = sumVisFibos (cast x) (cast y)
act ("vis_fibo" :: _) = sumVisFibos 20 38
act ["sleep",x]       = sleepMany (cast x)
act ("sleep" :: _)    = sleepMany 100
act _                 = countSequentially

-- `sigs` is used to block the default handling of the listed signals.
covering
run : (threads : Subset Nat IsSucc) -> List String -> IO ()
run threads args = app threads sigs posixPoller $ handle handlers (act args)
  where
    sigs : List Signal
    sigs = case args of
      "race"::_ => [SIGINT]
      _         => []

    handlers : All (Handler () e) [Errno]
    handlers = [\x => stderrLn "Error: \{errorText x} (\{errorName x})"]

covering
main : IO ()
main = do
  _::t <- getArgs | _ => die "Invalid arguments"
  n    <- asyncThreads
  run n t
```

<!-- vi: filetype=idris2:syntax=markdown
-->
