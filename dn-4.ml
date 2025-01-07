(*
Pri tej nalogi boste napisali svoj simulator Turingovih strojev. Zaradi preprostosti bomo za abecedo
vzeli kar znake tipa char, za prazni znak bomo izbrali presledek ' ', stanja pa bomo predstavili z nizi.
Za možne premike zafiksiramo tip direction:
*)

type direction = Left | Right
type state = string

(*
Napišite modul Tape, ki implementira spodnjo signaturo, kjer je:

    t tip v obe smeri neomejenih trakov in glavo na danem mestu;

    make, ki naredi nov trak z znaki iz niza ter glavo na prvem znaku;

    read, ki vrne znak pod glavo;

    write, ki pod glavo zapiše dani znak;

    move, ki glavo premakne v dano smer;

    print, ki izpiše vsebino traku ter pod njim z ^ označi mesto glave.

Zadnji dve funkciji naj vrneta nov trak, obstoječega pa naj pustita nespremenjenega.

Ker je tip t abstrakten, si lahko privoščite poljubno implementacijo, zato poskrbite tako za učinkovitost kot za preglednost kode.
*)

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

  let make chars =
    ([], List.init (String.length chars) (String.get chars))

  let move direction (left, right) =
    match direction with
      | Left -> (match left with
        | [] -> ([], ' ' :: right)
        | h :: t -> (t, h :: right)
      )
      | Right -> (match right with
        | [] -> (' ' :: left, [])
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

let _ =
Tape.(
  make "ABCDE"
  |> move Right
  |> move Right
  |> write '!'
  |> move Left
  |> print
)

(*
Napišite modul Machine, ki implementira spodnjo signaturo, kjer je:

    t tip Turingovih strojev;

    make, ki naredi nov stroj z danim začetnim stanjem in seznamom preostalih stanj ter prazno prehodno funkcijo;

    initial, ki vrne začetno stanje stroja;

    add_transition, ki prehodno funkcijo razširi s prehodom (q, a) -> (q', a', d);

    step, ki za dano stanje in trak izvede en korak stroja, če je to mogoče.

Zadnji dve funkciji naj vrneta spremenjene vrednosti, obstoječe argumente pa naj pustita nespremenjene. Prav tako pri zadnjih dveh funkcijah lahko predpostavite, da ju bomo klicali le na poprej podanih stanjih.

Tudi tu je tip t abstrakten, zato poskrbite za učinkovitost in preglednost kode.
*)

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

(*
Zapišite funkciji slow_run in speed_run tipa Machine.t -> str -> unit, ki simulirata Turingov stroj
na traku, na katerem je na začetku zapisan dani niz. Prva naj izpiše trakove in stanja pri vseh vmesnih
korakih, druga pa naj izpiše le končni trak. Slednjo bomo uporabljali tudi pri meritvi učinkovitosti izvajanja.
*)

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
      | Some (state', tape') ->
        run state' tape'
  in
  run (Machine.initial machine) (Tape.make tape)

let _ = slow_run binary_increment "1011"

let speed_run machine tape =
  let rec run state tape =
    match Machine.step machine state tape with
      | None -> tape
      | Some (state', tape') ->
        run state' tape'
  in
  let final = run (Machine.initial machine) (Tape.make tape) in
  Tape.print final

let _ = speed_run binary_increment "1011"

(*
Ko definiramo Turingov stroj, prehode običajno združujemo najprej po stanjih, nato pa še po znakih.
Prav tako pri dosti prehodih samo premikamo glavo, trak in stanje pa pustimo pri miru. Zapišite funkcije:

    for_state

    for_character

    for_characters

    move

    switch_and_move

    write_and_move

    write_switch_and_move

s katerimi bi lahko zgornji primer na krajše zapisali kot spodaj. Implementacijo in tipe ugotovite sami.
*)

(* TOOD *)

let binary_increment' =
  Machine.make "right" ["carry"; "done"]
  |> for_state "right" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ switch_and_move "carry" Left
  ]
  |> for_state "carry" [
    for_character '1' @@ switch_and_move "carry" Left;
    for_characters "0 " @@ write_switch_and_move "done" '1' Left
  ]
