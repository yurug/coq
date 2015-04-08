type 'a t = 'a u lazy_t
and 'a u =
  | Nil
  | Cons of 'a * 'a t

let (!!) = Lazy.force

let nil = Lazy.from_val Nil
let cons x xs = Lazy.from_val (Cons (x, xs))

let destruct t =
  match !! t with
  | Nil -> None
  | Cons (x, xs) -> Some (x, xs)

let rec map f lst =
  lazy (
    match !! lst with
    | Nil -> Nil
    | Cons (x, xs) -> Cons (f x, map f xs)
  )

let rec append xs ys =
  lazy (
    match !! xs with
    | Nil -> !! ys
    | Cons (x, xs) -> Cons (x, append xs ys)
  )

let rec concat t =
  lazy (
    match !! t with
    | Nil -> Nil
    | Cons (xs, xss) -> !! (append xs (concat xss))
  )

let return x = cons x nil

let ( >>= ) x f = concat (map f x)
