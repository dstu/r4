# r4: for comprehensions for Rust

This package provides the `iterate!` macro, which builds for comprehensions out
of nested flat-map operations. If you're familiar with Python's list
comprehensions or Scala's for statement, the syntax should be familiar.

See [rustdocs](https://docs.rs/r4) for usage, examples, and a more detailed
description of the macro's internals.

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
