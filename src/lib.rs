use std::iter::Iterator;

// Flattening iterator, which concatenates iterators provided by the wrapped
// iterator.
pub struct FlatIter<I: Iterator> where <I as Iterator>::Item: Iterator {
    wrapped: I,
    current_iterator: Option<<I as Iterator>::Item>,
}

impl<I: Iterator> FlatIter<I> where <I as Iterator>::Item: Iterator {
    pub fn new(wrapped: I) -> Self {
        FlatIter { wrapped: wrapped, current_iterator: None, }
    }

    // Pull in the next iterator from the wrapped iterator and return false iff
    // the wrapped iterator is exhausted.
    fn advance_wrapped(&mut self) -> bool {
        self.current_iterator = self.wrapped.next();
        self.current_iterator.is_some()
    }
}

impl<I: Iterator> Iterator for FlatIter<I> where <I as Iterator>::Item: Iterator {
    type Item = <<I as Iterator>::Item as Iterator>::Item;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        loop {
            if let Some(ref mut i) = self.current_iterator {
                let next = i.next();
                if next.is_some() {
                    return next;
                }
            }
            // Fall-through: current_iterator is empty.
            if !self.advance_wrapped() {
                return None;
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.current_iterator {
            Some(ref i) => {
                match i.size_hint() {
                    (min, None) => (min, None),
                    (_, Some(max)) => (max, None),
                }
            },
            // Either we're exhausted, or iteration hasn't yet begun.
            None => (0usize, None),
        }
    }
}

// Main entrypoint for iteration via for comprehensions. Accepts expressions
// like:
//
// (for x in xs; (if a;|let b = c;)*)+ yield r
//
// Expressions are compiled into nested flat_map operations via closures that
// move out of the enclosing environment. See package-level documentation for
// details.
macro_rules! iterate {
    ($($rest:tt)*) => ({ use ::r4::FlatIter; iterate_helper![$($rest)*] });
}

// Helper macro which iterate! delegates to. Do not call this directly unless
// you have good reason to.
macro_rules! iterate_helper {
    // Implementation note: adjacent wildcard matches aren't allowed, so each
    // recursive rule has three cases, wherein the wildcards matches are
    // separated by macro keywords.

    // yield
    (yield $r:expr) => (Some($r).into_iter());
    // for
    (for $x:ident in $xs:expr; $($rest:tt)*) =>
        ($xs.flat_map(move |$x| { iterate_helper![$($rest)*] }));
    // if if => if
    (if $a:expr; if $b:expr; $(if $c:expr;)* for $($rest:tt)*) =>
        (iterate_helper![if $a && $b $(&& $c)*; for $($rest)*]);
    (if $a:expr; if $b:expr; $(if $c:expr;)* let $($rest:tt)*) =>
        (iterate_helper![if $a && $b $(&& $c)*; let $($rest)*]);
    (if $a:expr; if $b:expr; $(if $c:expr;)* yield $($rest:tt)*) =>
        (iterate_helper![if $a && $b $(&& $c)*; yield $($rest)*]);
    // if
    (if $a:expr; for $($rest:tt)*) =>
        (FlatIter::new((if $a { Some(iterate_helper![for $($rest)*]) } else { None }).into_iter()));
    (if $a:expr; let $($rest:tt)*) =>
        (FlatIter::new((if $a { Some(iterate_helper![let $($rest)*]) } else { None }).into_iter()));
    (if $a:expr; yield $($rest:tt)*) =>
        (FlatIter::new((if $a { Some(iterate_helper![yield $($rest)*]) } else { None }).into_iter()));
    // let
    ($(let $lhs:pat = $rhs:expr;)+ for $($rest:tt)*) =>
        ({ $(let $lhs = $rhs;)+ iterate_helper![for $($rest)*] });
    ($(let $lhs:pat = $rhs:expr;)+ if $($rest:tt)*) =>
        ({ $(let $lhs = $rhs;)+ iterate_helper![if $($rest)*] });
    ($(let $lhs:pat = $rhs:expr;)+ yield $($rest:tt)*) =>
        ({ $(let $lhs = $rhs;)+ iterate_helper![yield $($rest)*] });
}
