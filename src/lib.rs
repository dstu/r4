// -*- mode: rust; rust-indent-offset: 4; -*-

//! Provides a macro that generates an iterable sequence via for comprehensions
//! (AKA list comprehensions).
//!
//! If you're familiar with [Python's list
//! comprehensions](https://docs.python.org/3/tutorial/datastructures.html#list-comprehensions)
//! or [Scala's for
//! comprehensions](https://docs.scala-lang.org/tour/for-comprehensions.html),
//! this should be familiar. The use of the `yield` keyword is also similar to
//! that of the recent [generator syntax
//! RFC](https://github.com/rust-lang/rfcs/blob/master/text/2033-experimental-coroutines.md).
//!
//! # Examples
//!
//! Sequences are built out of `for` statements, which may be nested.
//!
//! ```rust
//! #[macro_use(iterate)] extern crate r4;
//!
//! # fn main() {
//! let v: Vec<i32> = iterate![for x in 0..5; yield x * 2].collect();
//! assert_eq!(v, vec![0, 2, 4, 6, 8]);
//! # }
//! ```
//!
//! Multiple `for` statements are treated like nested loops.
//!
//! ```rust
//! # #[macro_use(iterate)] extern crate r4;
//! # fn main() {
//! #[derive(Debug, Eq, PartialEq)]
//! struct Item { x: i32, y: i32, }
//!
//! let v: Vec<Item> = iterate![for x in 0..3;
//!                             for y in 5..7;
//!                             yield Item { x: x, y: y, }]
//!                    .collect();
//!
//! let mut w: Vec<Item> = Vec::new();
//! for x in 0..3 {
//!   for y in 5..7 {
//!     w.push(Item { x: x, y: y, });
//!   }
//! }
//! assert_eq!(v, w);
//! # }
//! ```
//!
//! Stand-alone values may be `yield`ed.
//!
//! ```rust
//! # #[macro_use(iterate)] extern crate r4;
//! # fn main() {
//! let v: Vec<i32> = iterate![yield 0; yield 2; yield 4; yield 6; yield 8].collect();
//! assert_eq!(v, vec![0, 2, 4, 6, 8]);
//! # }
//! ```
//!
//! Intermediate variables may be bound with `let`, which may take a pattern.
//!
//! ```rust
//! # #[macro_use(iterate)] extern crate r4;
//! # fn main() {
//! let v: Vec<i32> = iterate![for x in 0..6; let y = x * 2; yield x * y].collect();
//! assert_eq!(v, vec![0, 2, 8, 18, 32, 50]);
//!
//! struct Item { x: i32, y: i32, }
//! let v: Vec<i32> = iterate![for x in 0..3;
//!                            for y in 5..7;
//!                            let item = Item { x: x, y: y, };
//!                            let Item { x: a, y: b, } = item;
//!                            yield a;
//!                            yield b]
//!                   .collect();
//! assert_eq!(v, vec![0, 5, 0, 6, 1, 5, 1, 6, 2, 5, 2, 6]);
//! # }
//! ```
//!
//! Iteration may be short-circuited via `if`.
//!
//! ```rust
//! # #[macro_use(iterate)] extern crate r4;
//! # fn main() {
//! let v: Vec<i32> = iterate![for x in 0..10; if x % 2 == 0; yield x].collect();
//! assert_eq!(v, vec![0, 2, 4, 6, 8]);
//! ```
//!
//! A pattern-based guard may be employed via `if let`.
//!
//! ```rust
//! # #[macro_use(iterate)] extern crate r4;
//! # fn main() {
//! fn process(a: i32) -> Option<i32> {
//!   if a % 2 == 0 {
//!     Some(a)
//!   } else {
//!     None
//!   }
//! }
//!
//! let v: Vec<i32> = iterate![for x in 0..10;
//!                            if let Some(y) = process(x);
//!                            yield y]
//!                   .collect();
//! assert_eq!(v, vec![0, 2, 4, 6, 8]);
//! # }
//! ```
//!
//! # Expressions
//!
//! See [the macro](macro.iterate.html) for a full breakdown of expressions it
//! recognizes. In brief, they are:
//!
//! * `for x in xs`: introduces a new scope that iterates over `xs`, binding the pattern
//!   `x` to each of its values.
//! * `if cond`: short-circuits subsequent expressions if `cond` is not `true`.
//! * `if let pattern = expr`: introduces a new scope that binds `pattern` to `expr`,
//!   short-circuiting subsequent expressions if `pattern` does not match `expr`.
//! * `let a = b`: introduces a new scope that binds `a` (which may be a pattern) to `b`.
//! * `yield r`: emits the value of the expression `r`.
//!
//! # Example expansion
//!
//! This macro invocation:
//!
//! ```rust
//! #[macro_use(iterate)] extern crate r4;
//! # fn main() {
//! let items = iterate![for x in 0..10;
//!                      let y = x + 1;
//!                      if y % 2 == 0;
//!                      let z = y + 3;
//!                      for x_prime in z..(z + 3);
//!                      yield x_prime];
//! # let v: Vec<i32> = items.collect();
//! # assert_eq!(v, vec![5, 6, 7, 7, 8, 9, 9, 10, 11, 11, 12, 13, 13, 14, 15]);
//! # }
//! ```
//!
//! is expanded like so:
//!
//! ```rust
//! extern crate r4;
//! # fn main() {
//! let items = {
//!   (0..10).flat_map(move |x| {
//!     let y = x + 1;
//!     r4::FlatIter::new(if y % 2 == 0 {
//!                         Some({ let z = y + 3;
//!                                (z..(z + 3)).flat_map(move |x_prime| {
//!                                                        ::std::iter::once(x_prime)
//!                                                      })
//!                              })
//!                       } else {
//!                         None
//!                       })
//!   })
//! };
//! # let v: Vec<i32> = items.collect();
//! # assert_eq!(v, vec![5, 6, 7, 7, 8, 9, 9, 10, 11, 11, 12, 13, 13, 14, 15]);
//! # }
//! ```
//!
//! # Lifetimes and moved values
//!
//! You can see in the example expansion above that the closures which
//! `iterate!` creates move variables that they refer to out of their
//! surrounding environment. This is done for lack of a better mechanism for
//! ensuring that the iterator created by `iterate!` doesn't outlive values
//! referred to by the closures it generates. This makes it possible for an
//! `iterate!`-derived macro to own its data, as in:
//!
//! ```rust
//! # #[macro_use(iterate)] extern crate r4;
//! fn generate_values() -> Box<Iterator<Item=u32>> {
//!   let xs = vec![1, 2, 3, 4];
//!   Box::new(iterate![for x in 0..10; if xs.contains(&x); yield 2 * x])
//! }
//! # fn main() {
//! # let v: Vec<u32> = generate_values().collect();
//! # assert_eq!(v, vec![2, 4, 6, 8]);
//! # }
//! ```
//!
//! As a result, if you refer to a non-`Copy` value from within an `iterate!`
//! macro, you will no longer be able to use that value.
//!
//! ```rust,ignore
//! # #[macro_use(iterate)] extern crate r4;
//! fn generate_values() -> Box<Iterator<Item=u32>> {
//!   let xs = vec![1, 2, 3, 4];
//!   let i = iterate![for x in 0..10; if xs.contains(&x); yield 2 * x];
//!   // We already moved `xs` into the iterator above, so we can't use it again.
//!   println!("xs are: {:?}", xs);  // Compilation error.
//!   Box::new(i)
//! }
//! ```
//!
//! This behavior can be circumvented by creating a borrow yourself, although
//! this will restrict the lifetime of the iterator to that of the borrow.
//!
//! ```rust
//! # #[macro_use(iterate)] extern crate r4;
//! # fn main() {
//! let xs = vec![1, 2, 3, 4];
//! let borrow = &xs;
//! // The iterators `i` and `j` are both limited to the lifetime of `borrow`,
//! // but they can share use of its data.
//! let i = iterate![for x in 0..10; if borrow.contains(&x); yield 2 * x];
//! let j = iterate![for x in 2..20; if borrow.contains(&x); yield 2 * x];
//! let v: Vec<i32> = i.chain(j).collect();
//! assert_eq!(v, vec![2, 4, 6, 8, 4, 6, 8]);
//! # }
//! ```

use std::iter::Iterator;

/// Flat-maps an Option&lt;I&gt; where I: Iterator into the underlying iterator. You
/// probably don't need to use this type directly. It is used internally by the
/// `iterate!` macro.
///
/// This is useful because both branches of an `if` expression must have the
/// same type. In other words, the following is not valid:
///
/// ```rust,ignore
/// use std::iter;
/// # fn main() {
/// let a = 1;
/// let b = 2;
/// let k =
///   if a + b > b + b {
///     // Type is std::vec::IntoIter<i32>.
///     vec![0i32, 1, 2, 3, 4].into_iter()  // Type mismatch.
///   } else {
///     // Type is std::iter::Empty.
///     iter::empty()                       // Type mismatch.
///   };
/// # }
/// ```
///
/// We can get around this limitation by ensuring that both arms of an `if`
/// expression resolve to a `FlatIter<I>`:
///
/// ```rust
/// extern crate r4;
/// # fn main() {
/// let a = 1;
/// let b = 2;
/// let k =
///   if a + b > b + b {
///     // Type is r4::FlatIter<std::vec::IntoIter<i32>>.
///     r4::FlatIter::new(Some(vec![0, 1, 2, 3, 4].into_iter()))
///   } else {
///     // Type is compatible with r4::FlatIter<std::vec::IntoIter<i32>>.
///     r4::FlatIter::new(None)
///   };
/// # }
/// ```
pub struct FlatIter<I: Iterator> {
    wrapped: Option<I>,
}

impl<I: Iterator> FlatIter<I> {
    pub fn new(wrapped: Option<I>) -> Self {
        FlatIter { wrapped: wrapped, }
    }
}

impl<I: Iterator> Iterator for FlatIter<I> {
    type Item = <I as Iterator>::Item;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        match self.wrapped {
            Some(ref mut i) => i.next(),
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.wrapped {
            Some(ref i) => i.size_hint(),
            None => (0usize, Some(0usize)),
        }
    }
}

/// Produces an iterator over values `yield`ed in a sequence of
/// semicolon-separated expressions.
///
/// Expressions are compiled into nested flat_map operations via closures that
/// move out of the enclosing environment. See [top-level
/// documentation](./#lifetimes-and-moved-values) for details.
///
/// Implementation note: adjacent wildcard matches aren't allowed, so each
/// recursive rule has multiple cases, wherein wildcard matches are separated by
/// macro keywords.
#[macro_export]
macro_rules! iterate {
    // yield
    (yield $r:expr) => (::std::iter::once($r));
    // chained yield
    (yield $r:expr; for $($rest:tt)+) =>
        (iterate![yield $r].chain(iterate![for $($rest)+]));
    (yield $r:expr; if $($rest:tt)+) =>
        (iterate![yield $r].chain(iterate![if $($rest)+]));
    (yield $r:expr; let $($rest:tt)+) =>
        (iterate![yield $r].chain(iterate![let $($rest)+]));
    (yield $r:expr; yield $($rest:tt)+) =>
        (iterate![yield $r].chain(iterate![yield $($rest)+]));
    // for
    (for $x:pat in $xs:expr; $($rest:tt)*) =>
        ($xs.flat_map(move |$x| { iterate![$($rest)*] }));
    // if let
    (if let $x:pat = $e:expr; for $($rest:tt)*) =>
        ($crate::FlatIter::new(if let $x = $e { Some(iterate![for $($rest)*]) } else { None }));
    (if let $x:pat = $e:expr; if $($rest:tt)*) =>
        ($crate::FlatIter::new(if let $x = $e { Some(iterate![if $($rest)*]) } else { None }));
    (if let $x:pat = $e:expr; let $($rest:tt)*) =>
        ($crate::FlatIter::new(if let $x = $e { Some(iterate![let $($rest)*]) } else { None }));
    (if let $x:pat = $e:expr; yield $($rest:tt)*) =>
        ($crate::FlatIter::new(if let $x = $e { Some(iterate![yield $($rest)*]) } else { None }));
    // if if => if
    // This cuts down on the degree of FlatIter nesting when there are many  if guards in a row.
    (if $a:expr; if $b:expr; $(if $c:expr;)* for $($rest:tt)*) =>
        (iterate![if $a && $b $(&& $c)*; for $($rest)*]);
    (if $a:expr; if $b:expr; $(if $c:expr;)* let $($rest:tt)*) =>
        (iterate![if $a && $b $(&& $c)*; let $($rest)*]);
    (if $a:expr; if $b:expr; $(if $c:expr;)* yield $($rest:tt)*) =>
        (iterate![if $a && $b $(&& $c)*; yield $($rest)*]);
    // if
    (if $a:expr; for $($rest:tt)*) =>
        ($crate::FlatIter::new(if $a { Some(iterate![for $($rest)*]) } else { None }));
    (if $a:expr; let $($rest:tt)*) =>
        ($crate::FlatIter::new(if $a { Some(iterate![let $($rest)*]) } else { None }));
    (if $a:expr; yield $($rest:tt)*) =>
        ($crate::FlatIter::new(if $a { Some(iterate![yield $($rest)*]) } else { None }));
    // let
    ($(let $lhs:pat = $rhs:expr;)+ for $($rest:tt)*) =>
        ({ $(let $lhs = $rhs;)+ iterate![for $($rest)*] });
    ($(let $lhs:pat = $rhs:expr;)+ if $($rest:tt)*) =>
        ({ $(let $lhs = $rhs;)+ iterate![if $($rest)*] });
    ($(let $lhs:pat = $rhs:expr;)+ yield $($rest:tt)*) =>
        ({ $(let $lhs = $rhs;)+ iterate![yield $($rest)*] });
}

#[cfg(test)]
mod tests {
    use std::fmt::Display;

    fn check_match<N: PartialEq + Display, I: Iterator<Item=N>, J: Iterator<Item=N>>(mut i: I, mut j: J) {
        let mut n = 0usize;
        loop {
            match (i.next(), j.next()) {
                (None, None) => return,
                (Some(ref x), None) => panic!["Mismatch on item {}: {} vs. None", n, x],
                (None, Some(ref y)) => panic!["Mismatch on item {}: None vs. {}", n, y],
                (Some(ref x), Some(ref y)) => if x != y { panic!["Mismatch on item {}: {} vs. {}", n, x, y] },
            }
            n += 1;
        }
    }
    
    #[test]
    fn test_basic() {
        check_match(vec![1, 2, 3, 4, 5].into_iter(),
                    iterate![for i in 1..6; yield i]);
    }

    #[test]
    fn test_basic_if() {
        check_match(vec![0, 2, 4, 6, 8].into_iter(),
                    iterate![for i in 0..10;
                             if i % 2 == 0;
                             yield i]);
    }

    #[test]
    fn test_basic_if_let() {
        check_match(vec![1, 3, 5, 7, 9].into_iter(),
                    iterate![for i in 0..10;
                             if i % 2 == 0;
                             let z = i + 1;
                             yield z]);
    }

    // This fails to compile because the closures generated by iterate! may
    // outlive values. (Using values.into_iter() also fails.)
    // fn test_move_fail() {
    //     let values = vec![1, 2, 3, 4];
    //     iterate![for i in 0..10; for v in values.iter(); yield v];
    // }

    // This provides an example of how to refer to an external variable without
    // moving everything out of it.
    #[test]
    fn test_move_succeed() {
        let values = vec![1, 2, 3, 4];
        let vs = &values;
        check_match(vec![1, 2, 3, 4,
                         1, 2, 3, 4,
                         1, 2, 3, 4,
                         1, 2, 3, 4].into_iter(),
                    iterate![for i in 0..4;
                             for v in vs.iter();
                             yield *v]);
    }

    // Taking references like that is still prone to lifetime-checking,
    // however. The below also fails to compile.
    // fn test_move_fail() {
    //     let i = {
    //         let values = vec![1, 2, 3, 4];
    //         let vs = &values;
    //         iterate![for i in 0..4; for v in vs.iter(); yield *v]
    //     };
    //     for x in i {
    //         println!("{}", x)
    //     }
    // }

    #[test]
    fn test_nested_refs() {
        let values = vec![1, 2, 3, 4];
        let vs = &values;
        check_match(vec![1, 2, 3, 4,
                         1, 2, 3, 4,
                         1, 2, 3, 4,
                         1, 2, 3, 4].into_iter(),
                    iterate![for x in vs.iter();
                             for y in vs.iter();
                             yield *y]);
    }

    #[test]
    fn test_nested_refs_inner_if() {
        let values = vec![1, 2, 3, 4];
        let vs = &values;
        check_match(vec![2, 2, 2, 2].into_iter(),
                    iterate![for x in vs.iter();
                             for y in vs.iter();
                             if *y == 2;
                             yield *y]);
    }

    #[test]
    fn test_nested_refs_outer_let() {
        let values = vec![1, 2, 3, 4];
        let vs = &values;
        check_match(vec![5, 6, 7, 8,
                         6, 7, 8, 9,
                         7, 8, 9, 10,
                         8, 9, 10, 11].into_iter(),
                    iterate![for x in vs.iter();
                             let a = *x + 3;
                             for y in vs.iter();
                             yield *y + a]);
    }

    // Variable shadowing is allowed, even when variables differ by type. This
    // is consistent with ordinary "let".
    #[test]
    fn test_nested_refs_let_let_shadowing_1() {
        let values = vec![1, 2, 3, 4];
        let vs = &values;
        check_match(vec![2, 3, 4, 5,
                         2, 3, 4, 5,
                         2, 3, 4, 5,
                         2, 3, 4, 5].into_iter(),
                    iterate![for x in vs.iter();
                             let a = *x + 3;
                             for y in vs.iter();
                             let a = 1;
                             yield *y + a]);
    }

    #[test]
    fn test_nested_refs_let_let_shadowing_2() {
        let values = vec![1, 2, 3, 4];
        let vs = &values;
        check_match(vec![2, 3, 4, 5,
                         2, 3, 4, 5,
                         2, 3, 4, 5,
                         2, 3, 4, 5].into_iter(),
                    iterate![for x in vs.iter();
                             let a = *x + 3;
                             let a = 1;
                             for y in vs.iter();
                             yield *y + a]);
    }

    // The compiler will warn about unused loop variables.
    #[test]
    fn test_nested_refs_for_let_shadowing() {
        let values = vec![1, 2, 3, 4];
        let vs = &values;
        check_match(vec![5, 5, 5, 5,
                         6, 6, 6, 6,
                         7, 7, 7, 7,
                         8, 8, 8, 8].into_iter(),
                    iterate![for x in vs.iter();
                             let a = *x + 3;
                             for y in vs.iter();
                             let y = 1;
                             yield y + a]);
    }

    #[test]
    fn test_nested_refs_for_let_for_shadowing() {
        let values = vec![1, 2, 3, 4];
        let vs = &values;
        let other_values = vec![5, 6, 7, 8];
        let ys = &other_values;
        check_match(vec![5, 6, 7, 8,
                         5, 6, 7, 8,
                         5, 6, 7, 8,
                         5, 6, 7, 8].into_iter(),
                    iterate![for x in vs.iter();
                             let x = *x + 1;
                             for x in ys.iter();
                             yield *x]);
    }

    #[test]
    fn test_just_multiple_yields() {
        check_match(vec![0, 1, 2, 3, 4, 5].into_iter(),
                    iterate![yield 0;
                             yield 1;
                             yield 2;
                             yield 3;
                             yield 4;
                             yield 5]);
    }

    #[test]
    fn test_multiple_yields_liked_nested_loops() {
        check_match(vec![0, 5, 6, 7, 8, 9,
                         1, 5, 6, 7, 8, 9,
                         2, 5, 6, 7, 8, 9,
                         3, 5, 6, 7, 8, 9,
                         4, 5, 6, 7, 8, 9].into_iter(),
                    iterate![for x in 0..5;
                             yield x;
                             for y in 5..10;
                             yield y]);
    }

    #[test]
    fn test_multiple_yield_with_filter_1() {
      check_match(vec![0, 5, 6, 7, 8, 9,
                       1,
                       2, 5, 6, 7, 8, 9,
                       3,
                       4, 5, 6, 7, 8, 9].into_iter(),
                  iterate![for x in 0..5;
                           yield x;
                           if x % 2 == 0;
                           for y in 5..10;
                           yield y]);
    }

    #[test]
    fn test_multiple_yield_with_filter_2() {
      check_match(vec![0, 5, 6, 7, 8, 9,
                       2, 5, 6, 7, 8, 9,
                       4, 5, 6, 7, 8, 9].into_iter(),
                  iterate![for x in 0..5;
                           if x % 2 == 0;
                           yield x;
                           for y in 5..10;
                           yield y]);
    }

    #[test]
    fn test_simple_if_let() {
        check_match(vec![0, 1, 2, 3].into_iter(),
                    iterate![for x in 0..4;
                             if let Some(b) = Some(x);
                             yield b]);
    }

    #[test]
    fn test_if_let_filter() {
        check_match(vec![].into_iter(),
                    iterate![for x in 0..4;
                             let c = if x > 5 { Some(x) } else { None };
                             if let Some(b) = c;
                             yield b]);
    }

    #[test]
    fn test_if_let_if() {
        check_match(vec![0, 2].into_iter(),
                    iterate![for x in 0..4;
                             if let Some(b) = Some(x);
                             if b % 2 == 0;
                             yield b]);
    }

    #[test]
    fn test_if_let_let() {
        check_match(vec![0, 2, 4, 6].into_iter(),
                    iterate![for x in 0..4;
                             if let Some(b) = Some(x);
                             let c = b * 2;
                             yield c]);
    }

    #[test]
    fn test_if_let_for() {
        check_match(vec![0,
                         1, 2, 3,
                         1,
                         2, 3, 4,
                         2,
                         3, 4, 5].into_iter(),
                    iterate![for x in 0..3;
                             yield x;
                             if let Some(b) = Some(x);
                             for y in (b + 1)..(b + 4);
                             yield y]);
    }

    #[test]
    fn bind_pattern_in_for() {
        struct Item {
            x: u32,
            y: u32,
        };
        let items = (0..5).map(|x| Item { x: x, y: x * 2, });
        check_match(vec![0, 0, 1, 2, 2, 4, 3, 6, 4, 8].into_iter(),
                    iterate![for Item { x, y, } in items;
                             yield x; yield y]);
    }
}
