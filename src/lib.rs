// -*- mode: rust; rust-indent-offset: 4; -*-
use std::iter::Iterator;

// Flat-maps an Option<I> where I: Iterator into any underlying Iterator.
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

/// Main entrypoint for iteration via for comprehensions. Produces an iterator
/// over values `yield`ed in a sequence of semicolon-separated expressions.
///
/// Multiple `yield` expressions are permitted. If present, they will produce a
/// chained sequence of iterators. Iterator chaining functions according to the
/// scope of the closest preceding `for` statement.
///
/// For example, `iterate![yield 0; yield 1; yield 2]` produces the sequence `1,
/// 2, 3`, but `iterate![for x in 0..2; yield x; for y in 2..4; yield y]`
/// produces the sequence `0, 2, 3, 1, 2, 3`, as if you had written:
///
/// ```rust,ignore
/// for x in 0..2 {
///   yield x;
///   for y in 2..4 {
///     yield y;
///   }
/// }
/// ```
///
/// Expressions are:
///
/// * `for x in xs`: introduces a new scope that iterates over `xs`, binding `x`
/// to each of its values.
/// * `if cond`: short-circuits subsequent expressions if `cond` is not `true`.
/// * `if let pattern = expr`: introduces a new scope that binds `pattern` to `expr`,
///   short-circuiting subsequent expressions if `pattern` does not match `expr`.
/// * `let a = b`: introduces a new scope that binds `a` (which may be a pattern) to `b`.
/// * `yield r`: emits the value of the expression `r`.
///
/// Expressions are compiled into nested flat_map operations via closures that
/// move out of the enclosing environment. See the package README for details.
#[macro_export]
macro_rules! iterate {
    // Implementation note: adjacent wildcard matches aren't allowed, so each
    // recursive rule has three cases, wherein the wildcards matches are
    // separated by macro keywords.

    // yield
    (yield $r:expr) => (Some($r).into_iter());
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
