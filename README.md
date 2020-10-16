# rye

Rye is a minimal, x86-64-only experiment into adding fibers to Rust.

Rye exposes an API that allows spawning, scheduling, and deallocating fibers. This API, while
largely safe, rests on a lot of unsafe assumptions not necessarily guaranteed by the rust
compiler. This is just an experiment and you should not use it for anything critical.

Rye has no central place where fibers are registered. Instead, when a fiber is yielded to it
receives a handle to the yielding fiber.

## Example

```rust
use rye::{Fiber, AllocStack};

// Create the fiber
let (stack, fiber) = Fiber::spawn(AllocStack::new(4096), |main| {
    println!("Hello from fiber!");
    main.yield_to();
});

// Yield to the fiber and return. This prints:
//  Hello from main!
//  Hello from fiber!
//  Back to main!
println!("Hello from main!");
let fiber = fiber.yield_to();
println!("Back to main!");

// Reclaim stack to deallocate fiber
stack.reclaim(fiber);
```
