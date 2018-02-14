# r4: for comprehensions for Rust

This package provides the `iterate!` macro, which builds for comprehensions out
of nested flat-map operations. If you're familiar with Python's list
comprehensions or Scala's for statement, the syntax should be familiar.

The macro should be provided with a series of semicolon-separated statements,
ending with a `yield` statement. Permitted statements:
* `for x in xs`: Introduces a scope that iterates through `xs` and binds `x` to
  each element thereof. Successive `for` statements behave like nested loops, so
  `iterate![for x in xs; for y in ys; yield (x, y)]` will consist of `xs.len() *
  ys.len()` elements. Note that `x` may be a pattern.
* `let x = y`: Binds `x` (which may be a pattern, like `Some(foo)`) to the
  expression `y`.
* `if a`: Skips over any later statements and doesn't yield anything iff the
  boolean expression `a` isn't `true`.
* `if let a = b`: Binds the pattern `a` to the expression `b`, skipping over
  later statements and not yielding anything if the pattern doesn't match.
* `yield x`: Yields the given expression for an iteration.

The closures created by `iterate!` move values out of the surrounding
environment. This means that you could have trouble like this:

```rust
#[macro_use] extern crate r4;

let values = vec![1, 2, 3];
for x in iterate![for i in 0..10;
                  for v in values;  // This is evaluated inside of a closure
                                    // that moves values out of the above binding.
                  yield v] {
  println!("{}", x)
}
// values was moved and can't be used.
println!("{}", values.len())
```

This is done for lack of a better mechanism for ensuring that the iterator
created by `iterate!` doesn't outlive any values referred to by the closures it
generates.

## Example expansion
This macro invocation:

```rust
#[macro_use]
extern crate r4;

let items = iterate![for x in 0..10;
                     let y = x + 1;
                     if y % 2 == 0;
                     let z = y + 3;
                     for x_prime in z..(z + 3);
                     yield x_prime];
```

is expanded like so:

```rust
#[macro_use] extern crate r4;

let items = {
  (0..10).flat_map(move |x| {
    let y = x + 1;
    ::r4::FlatIter::new(if y % 2 == 0 {
                          Some({ let z = y + 3;
                                 (z..(z + 3)).flat_map(move |x_prime| {
                                                         Some(x_prime).into_iter()
                                                       })
                              })
                        } else {
                          None
                        })
  });
};
```

# To-do
 - Examine overhead introduced by nesting closures instead of using naked loops.
 - Benchmark.
 - ?Figure out how to avoid moving values we don't have to.
 - ?Figure out how to avoid creating some new iterators unnecessarily.

# Copyright

Copyright 2015-2018, Donald S. Black.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use
this file except in compliance with the License.  You may obtain a copy of the
License at http://www.apache.org/licenses/LICENSE-2.0.

Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.  See the License for the
specific language governing permissions and limitations under the License.
