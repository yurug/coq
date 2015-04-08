type 'a t (* = 'a u lazy_t
and 'a u =
  | Nil
  | Cons of 'a * 'a t
  *)

val nil : 'a t
val cons : 'a -> 'a t -> 'a t

val destruct : 'a t -> ('a * 'a t) option

val map : ('a -> 'b) -> 'a t -> 'b t

val append : 'a t -> 'a t -> 'a t

val concat : 'a t t -> 'a t

val return : 'a -> 'a t
val (>>=)  : 'a t -> ('a -> 'b t) -> 'b t 
