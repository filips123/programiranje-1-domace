(*----------------------------------------------------------------------------*
 # 4. domača naloga
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Pri tej nalogi boste napisali svoj simulator Turingovih strojev. Zaradi
 preprostosti bomo za abecedo vzeli kar znake tipa `char`, za prazni znak bomo
 izbrali presledek `' '`, stanja pa bomo predstavili z nizi. Za možne premike
 zafiksiramo tip `direction`:
[*----------------------------------------------------------------------------*)

type direction = Left | Right
type state = string

(*----------------------------------------------------------------------------*
 ## Implementacija trakov
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite modul `Tape`, ki implementira spodnjo signaturo, kjer je:

 - `t` tip v obe smeri neomejenih trakov in glavo na danem mestu;
 - `make`, ki naredi nov trak z znaki iz niza ter glavo na prvem znaku;
 - `read`, ki vrne znak pod glavo;
 - `write`, ki pod glavo zapiše dani znak;
 - `move`, ki glavo premakne v dano smer;
 - `print`, ki izpiše vsebino traku (brez presledkov na začetku in koncu) ter
 pod njim z `^` označi mesto glave.

 Zadnji dve funkciji naj vrneta nov trak, obstoječega pa naj pustita
 nespremenjenega.

 Ker je tip `t` abstrakten, si lahko privoščite poljubno implementacijo, zato
 poskrbite tako za učinkovitost kot za preglednost kode.
[*----------------------------------------------------------------------------*)

module type TAPE = sig
  type t

  val make : string -> t
  val move : direction -> t -> t
  val read : t -> char
  val write : char -> t -> t
  val print : t -> unit
end

module Tape : TAPE = struct

  (* Left: (Head, -Inf) *)
  (* Right: [Head, +Inf) *)
  type t = char list * char list

  let rtrim string =
    let len = String.length string in
    let rec last idx =
      if idx < 0 || string.[idx] <> ' ' then idx
      else last (idx - 1)
    in
    let idx = last (len - 1) in
    String.sub string 0 (idx + 1)

  let ltrim string =
    let len = String.length string in
    let rec first idx =
      if idx >= len || string.[idx] <> ' ' then idx
      else first (idx + 1)
    in
    let idx = first 0 in
    String.sub string idx (len - idx)

  let empty list =
    list == [] || list == [' ']

  let make string =
    let string' = rtrim string in
    ([], List.init (String.length string') (String.get string'))

  let move direction (left, right) =
    match direction with
      | Left -> (match left with
        | [] when empty right -> ([], [])
        | [] -> ([], ' ' :: right)
        | ' ' :: t when empty right -> (t, [])
        | h :: t -> (t, h :: right)
      )
      | Right -> (match right with
        | [] when empty left -> ([], [])
        | [] -> (' ' :: left, [])
        | ' ' :: t when empty left -> ([], t)
        | h :: t -> (h :: left, t)
      )

  let read (_, right) =
    match right with
      | [] -> ' '
      | h :: _ -> h

  let write char (left, right) =
    match right with
      | [] -> (left, [char])
      | _ :: t -> (left, char :: t)

  let print (left, right) =
    let rec print_list = function
      | [] -> ()
      | h :: t -> print_char h; print_list t
    in
    print_list (List.rev left);
    print_list right;
    print_newline ();
    print_string (String.make (List.length left) ' ');
    print_char '^';
    print_newline ()

end

let primer_trak_1 = Tape.(
  make "ABCDE"
  |> move Right
  |> move Right
  |> write '!'
  |> move Left
  |> print
)
(*
AB!DE
 ^
*)
(* val primer_trak_1 : unit = () *)

let primer_trak_2 = Tape.(
  make "ABCDE"
  |> move Left
  |> move Left
  |> move Right
  |> move Right
  |> move Right
  |> move Right
  |> write '!'
  |> print
)
(*
AB!DE
  ^
*)
(* val primer_trak_2 : unit = () *)

(*----------------------------------------------------------------------------*
 ## Implementacija Turingovih strojev
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite modul `Machine`, ki implementira spodnjo signaturo, kjer je:

 - `t` tip Turingovih strojev;
 - `make`, ki naredi nov stroj z danim začetnim stanjem in seznamom preostalih
 stanj ter prazno prehodno funkcijo;
 - `initial`, ki vrne začetno stanje stroja;
 - `add_transition`, ki prehodno funkcijo razširi s prehodom $(q, a) \mapsto
 (q', a', d)$;
 - `step`, ki za dano stanje in trak izvede en korak stroja, če je to mogoče.

 Zadnji dve funkciji naj vrneta spremenjene vrednosti, obstoječe argumente pa
 naj pustita nespremenjene. Prav tako pri zadnjih dveh funkcijah lahko
 predpostavite, da ju bomo klicali le na poprej podanih stanjih.

 Tudi tu je tip `t` abstrakten, zato poskrbite za učinkovitost in preglednost
 kode.
[*----------------------------------------------------------------------------*)

module type MACHINE = sig
  type t
  val make : state -> state list -> t
  val initial : t -> state
  val add_transition : state -> char -> state -> char -> direction -> t -> t
  val step : t -> state -> Tape.t -> (state * Tape.t) option
end

module Machine : MACHINE = struct

  module StateHeadMap = Map.Make(
    struct
      type t = state * char
      let compare (s1, c1) (s2, c2) =
        let states = String.compare s1 s2 in
        let heads = Char.compare c1 c2 in
        if states <> 0 then states else heads
    end
  )

  type t = {
    initial : state;
    states : state list;
    transitions : (state * char * direction) StateHeadMap.t
  }

  let make initial states = {
    initial = initial;
    states = initial :: states;
    transitions = StateHeadMap.empty;
  }

  let initial machine = machine.initial

  let add_transition state head state' head' direction machine = {
    machine with
    transitions = StateHeadMap.add (state, head) (state', head', direction) machine.transitions
  }

  let step machine state tape =
    let head = Tape.read tape in
    let transition = StateHeadMap.find_opt (state, head) machine.transitions in
    match transition with
      | None -> None
      | Some (state', head', direction) ->
        let tape' = tape |> Tape.write head' |> Tape.move direction in
        Some (state', tape')

end

(*----------------------------------------------------------------------------*
 Primer stroja "Binary Increment" na <http://turingmachine.io> lahko
 implementiramo kot:
[*----------------------------------------------------------------------------*)

let binary_increment =
  Machine.(
    make "right" [ "carry"; "done" ]
    |> add_transition "right" '1' "right" '1' Right
    |> add_transition "right" '0' "right" '0' Right
    |> add_transition "right" ' ' "carry" ' ' Left
    |> add_transition "carry" '1' "carry" '0' Left
    |> add_transition "carry" '0' "done" '1' Left
    |> add_transition "carry" ' ' "done" '1' Left
  )

(* val binary_increment : Machine.t = <abstr> *)

(*----------------------------------------------------------------------------*
 Zapišite funkciji `slow_run` in `speed_run` tipa `Machine.t -> str -> unit`, ki
 simulirata Turingov stroj na traku, na katerem je na začetku zapisan dani niz.
 Prva naj izpiše trakove in stanja pri vseh vmesnih korakih, druga pa naj izpiše
 le končni trak. Slednjo bomo uporabljali tudi pri meritvi učinkovitosti
 izvajanja.
[*----------------------------------------------------------------------------*)

let slow_run machine tape =
  let rec run state tape =
    print_endline "Tape";
    Tape.print tape;
    print_endline "";
    print_endline "State";
    print_string state;
    print_endline "";
    print_endline "";
    print_endline "-----";
    print_endline "";
    match Machine.step machine state tape with
      | None -> ()
      | Some (state', tape') -> run state' tape'
  in
  run (Machine.initial machine) (Tape.make tape)

let primer_slow_run =
  slow_run binary_increment "1011"
(*
1011
^
right
1011
  ^
right
1011
  ^
right
1011
    ^
right
1011
    ^
right
1011
    ^
carry
1010
  ^
carry
1000
  ^
carry
1100
^
done
*)
(* val primer_slow_run : unit = () *)

let speed_run machine tape =
  let rec run state tape =
    match Machine.step machine state tape with
      | None -> tape
      | Some (state', tape') -> run state' tape'
  in
  let final = run (Machine.initial machine) (Tape.make tape) in
  Tape.print final

let primer_speed_run =
  speed_run binary_increment "1011"
(*
1100
^
*)
(* val primer_speed_run : unit = () *)

(*----------------------------------------------------------------------------*
 ## Krajši zapis
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Ko definiramo Turingov stroj, prehode običajno združujemo najprej po stanjih,
 nato pa še po znakih. Prav tako pri dosti prehodih samo premikamo glavo, trak
 in stanje pa pustimo pri miru. Zapišite funkcije:

 - `for_state`
 - `for_character`
 - `for_characters`
 - `move`
 - `switch_and_move`
 - `write_and_move`
 - `write_switch_and_move`

 s katerimi bi lahko zgornji primer na krajše zapisali kot spodaj.
 Implementacijo in tipe ugotovite sami.
[*----------------------------------------------------------------------------*)

let for_state (state : state) (transitions : (state -> Machine.t -> Machine.t) list list) (machine: Machine.t)
  : Machine.t =
  transitions
  |> List.flatten
  |> List.map (fun transition -> transition state)
  |> List.fold_left (fun machine' transition -> transition machine') machine

let for_characters (heads : string) (transition : char -> state -> Machine.t -> Machine.t)
  : (state -> Machine.t -> Machine.t) list =
  heads
  |> String.to_seq
  |> List.of_seq
  |> List.map transition

let for_character (head : char) (transition : char -> state -> Machine.t -> Machine.t)
  : (state -> Machine.t -> Machine.t) list =
  [transition head]

let move (direction : direction)
  : (char -> state -> Machine.t -> Machine.t) =
  fun head state machine -> Machine.add_transition state head state head direction machine

let switch_and_move (state' : state) (direction : direction)
  : (char -> state -> Machine.t -> Machine.t) =
  fun head state machine -> Machine.add_transition state head state' head direction machine

let write_and_move (head' : char) (direction : direction)
   : (char -> state -> Machine.t -> Machine.t) =
  fun head state machine -> Machine.add_transition state head state head' direction machine

let write_switch_and_move (head' : char) (state' : state) (direction : direction)
  : (char -> state -> Machine.t -> Machine.t) =
  fun head state machine -> Machine.add_transition state head state' head' direction machine

let binary_increment' =
  Machine.make "right" [ "carry"; "done" ]
  |> for_state "right" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ switch_and_move "carry" Left
  ]
  |> for_state "carry" [
    for_character '1' @@ write_switch_and_move '0' "carry" Left;
    for_characters "0 " @@ write_switch_and_move '1' "done" Left
  ]
(* val binary_increment' : Machine.t = <abstr> *)

let primer_krajsi_zapis =
  speed_run binary_increment' "1011"

(*----------------------------------------------------------------------------*
 ## Primeri Turingovih strojev
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Pri tej nalogi boste sestavljali stroje, ki bodo iz začetnega niza na traku na
 različne načine izračunali nov niz. Pri tem lahko predpostavite, da je začetni
 niz sestavljen iz ničel in enic, preostanek traku pa je prazen. Na koncu
 izvajanja naj bo glava na začetku novega niza, z izjemo tega niza pa naj bo
 trak prazen. Ni pa treba, da se izračunani niz začne na istem mestu na traku,
 kot se je začel prvotni niz.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ### Obračanje niza
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite Turingov stroj, ki začetni niz obrne na glavo.
[*----------------------------------------------------------------------------*)

(*

Prvi znak starega niza prestavimo na levo, kot zadnji znak obrnjenega
niza, ter ga izbrišemo. To ponavljamo za vsak znak.

Oznake:
- X: Konec prvotnega niza.
- Y: Začetek prvotnega niza.

Stanja:
- init: Poišče in označi konec niza.
- back: Gre nazaj do začetka niza in ga označi.
- search: Poišče naslednji znak.
- carry0: Nosi 0 nazaj do novega niza.
- carry1: Nosi 1 nazaj do novega niza.
- write0: Na prvo prosto mesto zapiše 0.
- write1: Na prvo prosto mesto zapiše 1.
- continue: Nadaljuje do konca novega niza.
- uninit: Pobriše označbo konca niza.
- return: Vrne se na začetek novega niza.
- done: Ustavi se.

*)

let reverse =
  Machine.make "init" [ "back"; "search"; "carry0"; "carry1"; "write0"; "write1"; "continue"; "uninit"; "return"; "done" ]
  |> for_state "init" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ write_switch_and_move 'X' "back" Left
  ]
  |> for_state "back" [
    for_characters "01" @@ move Left;
    for_character ' ' @@ write_switch_and_move 'Y' "search" Right
  ]
  |> for_state "search" [
    for_character ' ' @@ move Right;
    for_character '0' @@ write_switch_and_move ' ' "carry0" Left;
    for_character '1' @@ write_switch_and_move ' ' "carry1" Left;
    for_character 'X' @@ write_switch_and_move ' ' "uninit" Left
  ]
  |> for_state "carry0" [
    for_character ' ' @@ move Left;
    for_character 'Y' @@ switch_and_move "write0" Left
  ]
  |> for_state "carry1" [
    for_character ' ' @@ move Left;
    for_character 'Y' @@ switch_and_move "write1" Left
  ]
  |> for_state "write0" [
    for_characters "01" @@ move Left;
    for_character ' ' @@ write_switch_and_move '0' "continue" Right
  ]
  |> for_state "write1" [
    for_characters "01" @@ move Left;
    for_character ' ' @@ write_switch_and_move '1' "continue" Right
  ]
  |> for_state "continue" [
    for_characters "01" @@ move Right;
    for_character 'Y' @@ switch_and_move "search" Right
  ]
  |> for_state "uninit" [
    for_character ' ' @@ move Left;
    for_character 'Y' @@ write_switch_and_move ' ' "return" Left
  ]
  |> for_state "return" [
    for_characters "01" @@ move Left;
    for_character ' ' @@ switch_and_move "done" Right
  ]

let primer_reverse = speed_run reverse "0000111001"
(* 
1001110000          
^
*)
(* val primer_reverse : unit = () *)

(*----------------------------------------------------------------------------*
 ### Podvajanje niza
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite Turingov stroj, ki podvoji začetni niz.
[*----------------------------------------------------------------------------*)

(*

Vsak znak zaporedoma prenesemo za trenutno niz in ga podvojimo,
prvotni znak pa izbrišemo.

Oznake:
- X: Konec prvotnega niza.

Stanja:
- init: Poišče in označi konec niza.
- search: Poišče naslednji znak.
- read: Prebere trenutni znak.
- write-first-zero: Na konec novega niza napiše prvo ničlo.
- write-first-one: Na konec novega niza napiše prvo enko.
- write-second-zero: Na konec novega niza napiše drugo ničlo.
- write-second-one: Na konec novega niza napiše drugo enko.
- done: Ustavi se.

*)

let duplicate =
  Machine.make "init" [ "search"; "read"; "write-first-zero"; "write-first-one"; "write-second-zero"; "write-second-one"; "done" ]
  |> for_state "init" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ write_switch_and_move 'X' "search" Left
  ]
  |> for_state "search" [
    for_characters "01X" @@ move Left;
    for_character ' ' @@ switch_and_move "read" Right
  ]
  |> for_state "read" [
    for_character '0' @@ write_switch_and_move ' ' "write-first-zero" Right;
    for_character '1' @@ write_switch_and_move ' ' "write-first-one" Right;
    for_character 'X' @@ write_switch_and_move ' ' "done" Right;
  ]
  |> for_state "write-first-zero" [
    for_characters "01X" @@ move Right;
    for_character ' ' @@ write_switch_and_move '0' "write-second-zero" Right
  ]
  |> for_state "write-first-one" [
    for_characters "01X" @@ move Right;
    for_character ' ' @@ write_switch_and_move '1' "write-second-one" Right
  ]
  |> for_state "write-second-zero" [
    for_character ' ' @@ write_switch_and_move '0' "search" Left
  ]
  |> for_state "write-second-one" [
    for_character ' ' @@ write_switch_and_move '1' "search" Left
  ]

let primer_duplicate = speed_run duplicate "010011"
(* 
001100001111       
^
*)
(* val primer_duplicate : unit = () *)

(*----------------------------------------------------------------------------*
 ### Eniški zapis
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite Turingov stroj, ki na začetku na traku sprejme število $n$, zapisano
 v dvojiškem zapisu, na koncu pa naj bo na traku zapisanih natanko $n$ enic.
[*----------------------------------------------------------------------------*)

(*

Od prvotnega dvojiškega zapisa zaporedoma odštevamo 1, hkrati
pa v novem nizu vsakič dodamo novo enko.

Stanja:
- right: Pomakne se na konec dvojiškega zapisa.
- subtract: Od dvojiškega zapisa odšteje 1.
- transfer: Prenese enko do začetka eniškega zapisa.
- write: Zapiše enko na konec eniškega zapisa.
- return: Vrne se do konca dvojiškega zapisa.
- clear: Pobriše ostanke dvojiškega zapisa.
- done: Ustavi se.

*)

let to_unary =
  Machine.make "right" [ "subtract"; "transfer"; "write"; "return"; "clear"; "done" ]
  |> for_state "right" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ switch_and_move "subtract" Left
  ]
  |> for_state "subtract" [
    for_character '1' @@ write_switch_and_move '0' "transfer" Right;
    for_character '0' @@ write_switch_and_move '1' "subtract" Left;
    for_character ' ' @@ switch_and_move "clear" Right
  ]
  |> for_state "transfer" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ switch_and_move "write" Right
  ]
  |> for_state "write" [
    for_character '1' @@ move Right;
    for_character ' ' @@ write_switch_and_move '1' "return" Left
  ]
  |> for_state "return" [
    for_character '1' @@ move Left;
    for_character ' ' @@ switch_and_move "subtract" Left
  ]
  |> for_state "clear" [
    for_character '1' @@ write_and_move ' ' Right;
    for_character ' ' @@ switch_and_move "done" Right
  ]

let primer_to_unary = speed_run to_unary "1010"
(* 
1111111111
^
*)
(* val primer_to_unary : unit = () *)

(*----------------------------------------------------------------------------*
 ### Dvojiški zapis
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite ravno obratni Turingov stroj, torej tak, ki na začetku na traku
 sprejme število $n$ enic, na koncu pa naj bo na traku zapisano število $n$ v
 dvojiškem zapisu.
[*----------------------------------------------------------------------------*)

(*

Iz eniškega zapisa postopoma brišemo znake, hkrati pa v dvojiškem
zapisu prištevamo enke.

Stanja:
- init: Pomakne se do mesta dvojiškega zapisa.
- start: Začne pisati dvojiški zapis.
- next: Pomakne se do konca dvojiškega zapisa.
- remove: Pobriše prvo enko iz eniškega zapisa.
- transfer: Pomakne se do mesta dvojiškega zapisa.
- carry: Dvojiškemu zapisu prišteje enko.
- clear: Počisti ničle za sabo.
- return: Pomakne se na začetek dvojiškega zapisa.
- done: Ustavi se.

*)

let to_binary =
  Machine.make "init" [ "start"; "next"; "remove"; "transfer"; "carry"; "clear"; "return"; "done" ]
  |> for_state "init" [
    for_character '1' @@ move Left;
    for_character ' ' @@ switch_and_move "start" Left
  ]
  |> for_state "start" [
    for_character ' ' @@ write_switch_and_move '0' "next" Right
  ]
  |> for_state "next" [
    for_characters "10" @@ move Right;
    for_character ' ' @@ switch_and_move "remove" Right
  ]
  |> for_state "remove" [
    for_character '1' @@ write_switch_and_move '0' "transfer" Left;
    for_character '0' @@ move Right;
    for_character ' ' @@ switch_and_move "clear" Left
  ]
  |> for_state "transfer" [
    for_character '0' @@ move Left;
    for_character ' ' @@ switch_and_move "carry" Left
  ]
  |> for_state "carry" [
    for_character '1' @@ write_and_move '0' Left;
    for_characters "0 " @@ write_switch_and_move '1' "next" Right
  ]
  |> for_state "clear" [
    for_character '0' @@ write_and_move ' ' Left;
    for_character ' ' @@ switch_and_move "return" Left
  ]
  |> for_state "return" [
    for_characters "10" @@ move Left;
    for_character ' ' @@ switch_and_move "done" Right
  ]

let primer_to_binary = speed_run to_binary (String.make 42 '1')
(* 
101010                                           
^
*)
(* val primer_to_binary : unit = () *)
