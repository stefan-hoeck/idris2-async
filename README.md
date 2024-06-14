# idris2-async: Asynchronous computations in Idris2

This is a library for running cancelable asynchronous computations
with proper error handling in Idris2. Depending on the backend you
use, this also offers true parallelism, that is, computations running in
parallel on multicore systems. It was strongly inspired by the
[cats-effect](https://typelevel.org/cats-effect/) library written in
Scala, although it is by far not as battle hardened as is antetype.

This is a literate Idris source file, so you can compile and run it.
It is recommended to use [pack](https://github.com/stefan-hoeck/idris2-pack)
for building and running the example applications:

```sh
pack -o async exec docs/src/README.md [args]
```

Before we start, let's import a couple of modules:

```idris
module README

import Data.List
import IO.Async
import IO.Async.ThreadPool
import IO.Async.Scheduler
import System

%default total
```

## Introducing the `Async` Monad

This library provides a new data type `Async es a` for describing
cancelable, asynchronous computations that can fail with one of the errors
listed in `es` and yield a result of type `a` if all goes well.

Before we look at a first example, we need to get our terminology straight.

* synchronous: Synchronous computations are typically defined via
  `pure` or `liftIO`: They are the typical sequential effects we know
  from the `IO` monad.
* asynchronous: Asynchronous computations are defined using
  `async` or `cancelableAsync` and produce their result by invoking
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

In order to demonstrate the difference, we define two countdowns:
One for counting down seconds, the other counting down milliseconds
(in 100 ms steps):

```idris
countSeconds : Scheduler => Nat -> Async [] ()
countSeconds 0     = putStrLn "Second counter done."
countSeconds (S k) = do
  putStrLn "\{show $ S k} s left"
  sleep 1.s
  countSeconds k

countMillis : Scheduler => Nat -> Async [] ()
countMillis 0     = putStrLn "Millisecond counter done."
countMillis (S k) = do
  putStrLn "\{show $ S k * 100} ms left"
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
an operating system thread, even though we call `sleep`. I will explain this in
greater detail later when we talk about `Fiber`s, but for now suffice
to say that the `sleep` used above (from module `IO.Async.Scheduler.sleep`)
is more powerful than `System.sleep` from the base library although
they semantically do the same thing: They stop a sequence of computations
for a predefined amount of time.

Let's try and run the two countdowns sequentially:

```idris
countSequentially : Scheduler => Async [] ()
countSequentially = do
  putStrLn "Sequential countdown:"
  countSeconds 2
  countMillis 10
```

You can try this example by running `main` with the `"seq"` command-line
argument:

```sh
> pack -o async exec docs/src/README.md seq
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
to finish using `joinResult`. Here's the code:


```idris
countParallel : Scheduler => Async [] ()
countParallel = do
  putStrLn "Concurrent countdown"
  f1 <- start $ countSeconds 2
  f2 <- start $ countMillis 10
  joinResult f1
  joinResult f2
```

If you try this example by running `main` with the `"par"` argument, you will
notice that the messages from the two countdowns are now interleaved giving
at least the illusion of concurrency. However, just like `sleep` and unlike
`Prelude.threadWait`, `joinResult` will not block the current operating
system thread, and other computations could still run concurrently on the
current thread.

```sh
> pack -o async exec docs/src/README.md par
Condurrent countdown
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
countParallel2 : Scheduler => Async [] ()
countParallel2 = ignore $ par [ countSeconds 2, countMillis 10 ]
```

Another thing to do with two or more potentially long-running
computations is to run them concurrently until one of them
terminates. This would allow us to - for instance - run a
long-running computation until a timeout fires, in which case
we might want to end with an error. We will look at that example
later on. For now, let's just run our countdowns concurrently
until the faster of the two terminates:

```idris
raceParallel : Scheduler => Async [] ()
raceParallel =
  putStrLn "Racing countdowns" >> race [ countSeconds 10000, countMillis 10 ]
```

Running this with the `"race"` command-line argument gives the
following output:

```sh
> pack -o async exec docs/src/README.md race
Racing countdowns
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

sumFibos : Nat -> Nat -> Async [] ()
sumFibos nr fib = do
  vs <- parTraverse (\n => lazy (fibo n)) (replicate nr fib)
  printLn (sum vs)
```

You can try this by running the example application like so:

```sh
> pack -o async exec docs/src/README.md fibo 1000 20
10946000
```

The first numeric argument is the number of concurrent computations to
run (and thus, the number of fibers that will be created), the second
tells the application what Fibonacci number to compute. If you feel
adventurous, try increasing the number of fibers to one million.
This will undoubtedly consume quite a bit of memory and take more
than a minute to terminate, but terminate it will. It would be
unthinkable to create that number of operating system threads!

### But what about parallelism?

The ability to create an almost unlimited amount of concurrently
running computations is a big advantage of fibers. But what about
true parallelism? Can the computations actually be run on several
physical cores?

The answer to that depends on the backend we use. This example
application is supposed to be run on one of Idris's Scheme backends,
and can thus make use of more than one physical core. The core function for
running an `Async` computation is `IO.Async.Fiber.runAsyncWith`, which
takes an `ExecutionContext` as an implicit argument.

An `ExecutaionContext`'s main functionality is to provide function
`submit`, which allows us to enqueue an arbitrary `IO` action that
will then be processed by the execution context. One implementation
of this type is provided in module `IO.Async.ThreadPool`, which - just
as the name implies - uses a fixed-size pool of operating system
threads to process the enqueued `IO` actions. If the number of
threads is greater than one, we get true parallelism when processing
more than one fiber at a time.

Here is a way to visualize this behavior. We again compute Fibonacci
numbers, but this time we make sure that the numbers we compute are
large enough to take hundreds of milliseconds at the least. In addition,
we print ever result to get an idea of the runtime behavior:

```idris
sumVisFibos : Nat -> Nat -> Async [] ()
sumVisFibos nr fib = do
  vs <- parTraverse visFibo (replicate nr fib)
  printLn (sum vs)

  where
    visFibo : Nat -> Async [] Nat
    visFibo n = lazy (fibo n) >>= \x => printLn x $> x
```

Run this with the `"vis_fibo"` command-line argument, but before doing
this you might want to change the number of operating system threads
to use by setting environment variable `$IDRIS2_ASYNC_THREADS` (the
default is to use four threads):

```sh
export IDRIS2_ASYNC_THREADS="2"
pack -o async exec docs/src/README.md vis_fibo 10 42
```

With the arguments shown above, you will probably note
that the results are always printed pairwise in quick
succession before the app is again silent for a couple of
seconds. By changing the number of threads you might get
larger blocks of quickly printed results, an indicator that
several computations are indeed processed in parallel before
the next bunch of computations start.

### Cancelling fibers

The ability to create thousands of concurrent computations raises
the question about controlling them, in particular, about
cancelling them when they are no longer needed.

Fortunately, this can be easily done with the `cancel` action. As an
example - I took this from the cats-effect web page -
we generate three fibers running forever concurrently, and
cancel them all after a short delay.

First, we need some kind of random number generation. Since the Idris
standard libraries do not offer such a thing, I just quickly copied
the relevant code from contrib:

```idris
%foreign "scheme:blodwen-random"
         "javascript:lambda:(max)=>Math.floor(Math.random() * max)"
prim__randomBits32 : Bits32 -> PrimIO Bits32

randomRange : HasIO io => Bits32 -> Bits32 -> io Bits32
randomRange mi ma = (mi +) <$> primIO (prim__randomBits32 $ ma - mi)
```

Next, we define an action that prints a greeting after a random
delay, plus a utility for repeating an effect infinitely:

```idris
greet : Scheduler => (word, name : String) -> Async [] ()
greet word name = do
  t <- randomRange 100 700
  sleep (cast t).ms
  putStrLn "\{word}, \{name}"

covering
forever : Monad m => Lazy (m ()) -> m ()
forever x = x >> forever x
```

Finally, our greeting application asks for a name and keeps
printing greetings in three different languages until after
five seconds, the cacophony is fortunately stopped:

```idris
covering
greetApp : Scheduler => Async [] ()
greetApp = do
  putStrLn "Hello! What's your name?"
  n  <- getLine
  f1 <- start . forever $ greet "Hallo" n
  f2 <- start . forever $ greet "Bonjour" n
  f3 <- start . forever $ greet "Hola" n

  sleep 5.s
  traverse_ cancel [f1,f2,f3]

selfCancel : Async [] ()
selfCancel = do
  f <- start {es = []} $ do
    onCancel (uncancelable $ \_ => canceled >> putStrLn "I was canceled but still print") (putStrLn "Canceled!")
    putStrLn "This is not printed"
  o <- join f
  putStrLn $ case o of
    Succeeded res => "Thread succeeded. Oops"
    Canceled => "Thread was canceled. Yay!"
    Error err impossible
```

## The `main` function

This final sections only shows the `main` functions and a few utilities
used to run the examples in this introduction.

```idris
covering
act : Scheduler => List String -> Async [] ()
act ("par"   :: _)          = countParallel
act ("par2"  :: _)          = countParallel2
act ("race"  :: _)          = raceParallel
act ["fibo",x,y]            = sumFibos (cast x) (cast y)
act ("fibo" :: _)           = sumFibos 1000 30
act ["vis_fibo",x,y]        = sumVisFibos (cast x) (cast y)
act ("vis_fibo" :: _)       = sumVisFibos 20 38
act ("greet" :: _)          = greetApp
act ("self_cancel" :: _)    = selfCancel
act _                       = countSequentially

covering
run : (threads : Nat) -> {auto 0 _ : IsSucc threads} -> List String -> IO ()
run threads args = do
  sc <- newSchedulerST
  t  <- fork $ process sc
  app threads $ act @{sc} args
  stop sc
  threadWait t

covering
main : IO ()
main = do
  _::t <- getArgs | _ => die "Invalid arguments"
  s <- getEnv "IDRIS2_ASYNC_THREADS"
  case cast {to = Nat} <$> s of
    Just (S k) => run (S k) t
    _          => run 4 t
```

<!-- vi: filetype=idris2:syntax=markdown
-->
