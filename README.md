# forth-lisp

A prolog compiler written in lisp, written in forth.

## Usage

- The `:lisp` word (until `;`) changes the current mode to lisp mode.
- In lisp, the `<-` macro adds new rules to the database and the `?-` macro queries the database.
  ```forth
  :lisp
    (<- (member ?item (?item . ?rest)))
    (<- (member ?item (?x . ?rest)) (member ?item ?rest))

    (?- (member ?x (2 3 ? 5)))
  ;
  ```
