//! Example proc macro based on https://doc.rust-lang.org/book/ch19-06-macros.html
//!

/// The HelloMacro trait, should print hello message to stdout.
pub trait HelloMacro {
    fn hello_macro();
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
