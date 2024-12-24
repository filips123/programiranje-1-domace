set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 Definirajte funkcijo, ki _rekurzivno_ (torej naivno in ne direktno s formulo,
 ki jo boste morali dokazati) sešteje prvih `n` naravnih števil, ter
 dokažite, da zanjo velja znana enakost (najprej v obliki, ki ne zahteva
 deljenja, nato pa še v običajni obliki).
------------------------------------------------------------------------------/

def vsota_prvih : Nat → Nat :=
  fun n => match n with
  | .zero => Nat.zero
  | .succ m => n + vsota_prvih m

theorem gauss : (n : Nat) → 2 * vsota_prvih n = n * (n + 1) := by
  intro n
  induction n with
  | zero =>
    simp [vsota_prvih]
  | succ m ih =>
    simp [vsota_prvih]
    rw [Nat.mul_add]
    rw [ih]
    rw [← Nat.add_mul]
    rw [Nat.mul_comm]
    rw [Nat.add_assoc]
    have one_plus_one_is_two : 1 + 1 = 2 := by rfl
    rw [one_plus_one_is_two]
    have m_plus_2_is_2_plus_m : m + 2 = 2 + m := by rw [Nat.add_comm]
    rw [m_plus_2_is_2_plus_m]

theorem cisto_pravi_gauss : (n : Nat) → vsota_prvih n = (n * (n + 1)) / 2 := by
  intro n
  calc
    vsota_prvih n
      = (2 * vsota_prvih n) / 2 := by simp
    _ = (n * (n + 1)) / 2 := by rw [gauss]

/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje podobno kot na predavanjih, le da namesto svojih naravnih
 števil uporabimo vgrajena. Da se tipi ujamejo, funkcijo stikanja napišemo s
 pomočjo taktik.

 Napišite funkcijo `obrni`, ki vrne na glavo obrnjen vektor, ter funkciji
 `glava` in `rep`, ki varno vrneta glavo in rep _nepraznega_ seznama.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen => by rw [Nat.add_comm]; exact ys
  | .sestavljen x xs' => by rw [Nat.add_right_comm]; exact Vektor.sestavljen x (stakni xs' ys)

def obrni : {A : Type} → {n : Nat} → Vektor A n → Vektor A n :=
  fun xs => match xs with
  | .prazen => Vektor.prazen
  | .sestavljen x xs' => stakni (obrni xs') (Vektor.sestavljen x Vektor.prazen)

def glava : {A : Type} → {n : Nat} -> Vektor A (n + 1) -> A :=
  fun xs => match xs with
  | .sestavljen x _ => x

def rep : {A : Type} → {n : Nat} -> Vektor A (n + 1) -> Vektor A n :=
  fun xs => match xs with
  | .sestavljen _ xs' => xs'

/------------------------------------------------------------------------------
 ## Predikatni račun

 Dokažite spodnje tri trditve. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."
 Za dokaz potrebujete klasično logiko, torej nekaj iz modula `Classical`.
------------------------------------------------------------------------------/

theorem forall_implies : {A : Type} → {P Q : A → Prop} →
  (∀ x, (P x → Q x)) → (∀ x, P x) → (∀ x, Q x) := by
  intro A
  intro P Q
  intro PxQx
  intro Px
  intro x
  apply PxQx
  apply Px

theorem forall_implies' : {A : Type} → {P : Prop} → {Q : A → Prop} →
  (∀ x, (P → Q x)) ↔ (P → ∀ x, Q x) := by
  intro A
  intro PProp
  intro QProp
  constructor

  intro PQx
  intro P
  intro x
  apply PQx
  apply P

  intro PQx
  intro x
  intro P
  apply PQx
  apply P

theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) := by
  intro G
  intro P
  intro g
  apply Classical.byCases
  {
    -- Pijejo vsi
    intro _
    exists g
  }
  {
    -- Nekdo ne pije
    intro H
    have H' : ¬ ∀ x, P x := by
      intro nH'
      apply H
      intro _
      apply nH'
    let ⟨p, nPp⟩ := Classical.not_forall.mp H'
    exists p
    intro Pp
    exfalso
    exact nPp Pp
  }

/------------------------------------------------------------------------------
 ## Dvojiška drevesa

 Podan naj bo tip dvojiških dreves skupaj s funkcijama za zrcaljenje in izračun
 višine ter dvema funkcijama, ki obe od leve proti desni naštejeta elemente
 drevesa. Pri tem prva deluje naivno in ima časovno zahtevnost O(n log n), druga
 pa je malo bolj zapletena in deluje v času O(n). Dokažite spodnje enakosti, pri
 čemer lahko do pomožne funkcije `aux` dostopate kot `elementi'.aux`
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → Drevo A → A → Drevo A → Drevo A

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno l x d => .sestavljeno (zrcali d) x (zrcali l)

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno l _ d => 1 + max (visina l) (visina d)

def elementi : {A : Type} → Drevo A → List A :=
  fun t => match t with
  | .prazno => []
  | .sestavljeno l x d => elementi l ++ x :: elementi d

def elementi' : {A : Type} → Drevo A → List A :=
  let rec aux : {A : Type} → Drevo A → List A → List A :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno l x d => aux l (x :: aux d acc)
  fun t => aux t []

theorem zrcali_zrcali :
  {A : Type} → (t : Drevo A) →
  zrcali (zrcali t) = t := by
  intro A
  intro t
  induction t with
  | prazno =>
    simp [zrcali]
  | sestavljeno l x r il ir =>
    simp [zrcali]
    constructor
    rw [il]
    rw [ir]

theorem visina_zrcali :
  {A : Type} → (t : Drevo A) →
  visina (zrcali t) = visina t := by
  intro A
  intro t
  induction t with
  | prazno =>
    simp [zrcali]
  | sestavljeno l x r il ir =>
    simp [visina]
    rw [il, ir]
    rw [Nat.max_comm]

theorem elementi_elementi'_aux :
  {A : Type} → (t : Drevo A) → (acc : List A) →
  ∀ acc : List A, elementi t ++ acc = elementi'.aux t acc := by
  intro A
  intro t
  intro acc
  induction t with
  | prazno =>
    simp [elementi, elementi'.aux]
  | sestavljeno l x r il ir =>
    intro acc
    simp [elementi, elementi'.aux]
    rw [il, ir]

theorem elementi_elementi' :
  {A : Type} → (t : Drevo A) →
  elementi t = elementi' t := by
  intro A
  intro t
  simp [elementi']
  rw [← elementi_elementi'_aux t []]
  simp
