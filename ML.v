(** Coq implementation of the bimodal logic used in Charles Jarrett's _The Logical Structure of Spinoza's Ethics_ (http://www.jstor.org/stable/20115250). It is an adaptation of Christoph Benzmüller and Bruno Woltzenlogel Paleo's _Interacting with Modal Logics in the Coq Proof Assistant_ (http://page.mi.fu-berlin.de/cbenzmueller/papers/C44.pdf), modified to use two modal operators with appropriate accessibility relations. *)

Require Import Classical.
Require Import Coq.Logic.Classical_Pred_Type.

(* *)

(** * Syntax *)

(* *)

(** [ i ] := the type of worlds. *) 

Parameter i : Type. 

(** [ u ] := the type of individuals. *)

Parameter u : Type. 

(** [ o ] := the type of modal propositions. *)

Definition o := i -> Prop. 

(** ** Accessibility Relations *)

Inductive s : i -> i -> Prop := (* Accessibility relation for N and P *)
| s_reflexivity : forall w, s w w.

Inductive r : i -> i -> Prop := (* Accessibility relation for L and M *)
| r_s : forall w1 w2, s w1 w2 -> r w1 w2
| r_symmetry: forall w1 w2, (r w1 w2) -> (r w2 w1)
| r_transitivity: forall w1 w2 w3, (r w1 w2) -> (r w2 w3) -> (r w1 w3).

Theorem r_reflexivity : forall w, r w w.
intro. apply r_s. apply s_reflexivity. Qed.

(** ** Equality *)

Definition mequal (x y: u)(w: i) := x = y. 

Notation "x m= y" := (mequal x y) (at level 99, right associativity).
Definition mneq (x y: u)(w: i) := x <> y . 

Notation "x m<> y" := (mneq x y) (at level 74, right associativity).

(** ** Connectives *)

Definition mnot (p: o)(w: i) := ~ (p w). 

Notation "m~ p" := (mnot p) (at level 74, right associativity).

Definition mand (p q:o)(w: i) := (p w) /\ (q w). 

Notation "p m/\ q" := (mand p q) (at level 79, right associativity).

Definition mor (p q:o)(w: i) := (p w) \/ (q w).

Notation "p m\/ q" := (mor p q) (at level 79, right associativity).

Definition mimplies (p q:o)(w:i) := (p w) -> (q w).

Notation "p m-> q" := (mimplies p q) (at level 99, right associativity).

Definition mequiv (p q:o)(w:i) := (p w) <-> (q w). 

Notation "p m<-> q" := (mequiv p q) (at level 99, right associativity).

(** ** Quantifiers *)

Definition A {t: Type} (p: t -> o) (w: i) 
:= forall x, p x w. 

Notation "'mforall' x, p" := 
(A (fun x => p)) (at level 200, x ident, 
right associativity) : type_scope. 

Notation "'mforall' x : t , p" := 
(A (fun x:t => p)) (at level 200, x ident, right associativity,
format "'[' 'mforall' '/ ' x : t , '/ ' p ']'") : type_scope.

Definition E {t: Type} (p: t -> o) (w: i) 
:= exists x : t, p x w. 

Notation "'mexists' x , p" := (E (fun x => p)) 
(at level 200, x ident, right associativity) : type_scope. 

Notation "'mexists' x : t , p" := 
(E (fun x:t => p)) (at level 200, x ident, right associativity, 
format "'[' 'mexists' '/ ' x : t , '/ ' p ']'") : type_scope.

(** ** Modal Operators *)

Definition L (p: o) := 
fun w => forall w1, (r w w1) -> (p w1). 

Definition M (p: o) := 
fun w => exists w1, (r w w1) /\ (p w1).

Definition N (p: o) := 
fun w => forall w1, (s w w1) -> (p w1). 

Definition P (p: o) := 
fun w => exists w1, (s w w1) /\ (p w1).

(** ** Modal Validity *)

Definition V (p: o) := forall w, p w.

Notation "[ p ]" := (V p).

(* *)

(** * Tactics *)

(* *)

Ltac L_i := 
let w := fresh "w" in 
let R := fresh "R" in 
(intro w at top; intro R at top).

Ltac L_elim H w1 H1 :=
match type of H with ((L ?p) ?w) => cut (p w1);
[intros H1 | (apply (H w1); try assumption)] end.

Ltac L_e H H1:=
match goal with | [ |- (_ ?w) ] => L_elim H w H1 end.

Ltac M_e H :=
let w := fresh "w" in let R :=
fresh "R" in (destruct H as [w [R H]];
move w at top; move R at top).

Ltac M_i w :=
(exists w; split; [assumption | idtac]).

Ltac N_i := 
let w := fresh "w" in 
let R := fresh "R" in 
(intro w at top; intro R at top).

Ltac N_elim H w1 H1 :=
match type of H with ((N ?p) ?w) => cut (p w1);
[intros H1 | (apply (H w1); try assumption)] end.

Ltac N_e H H1:=
match goal with | [ |- (_ ?w) ] => N_elim H w H1 end.

Ltac P_e H :=
let w := fresh "w" in let R :=
fresh "R" in (destruct H as [w [R H]];
move w at top; move R at top).

Ltac P_i w :=
(exists w; split; [assumption | idtac]).

Ltac mv :=
match goal with [|- (V _)] => intro end.

(* *)

(** * Derived Rules *)

(* *)

Theorem R1 :
[ mforall p : o, L p m-> N p ].
mv. intros p H. N_i. L_e H H0; auto.
apply r_s. auto. Qed.

Theorem sT : (* = R2 *)
[ mforall p : o, (N p) m-> p ]. 
mv. intros p H. N_e H H0. auto.
apply s_reflexivity. Qed.

Theorem rK: (* = R3 *)
[ mforall p : o, mforall q : o,
(L (p m-> q)) m-> (L p) m-> (L q) ]. 
mv. intros p q H0 H1. L_i. 
L_e H0 H2. L_e H1 H3. auto.
Qed.

Theorem r5: (* = R4 *)
[ mforall p : o, (M p) m-> (L (M p)) ]. 
mv. intros p H. L_i. M_e H.
apply r_symmetry in R.
pose proof (r_transitivity w0 w w1 R R0).
M_i w1. auto. Qed.
(* The following formalization of R5 differs somewhat from the original, but it logically entails R5: If some P can be proved from 0 premises, it can certainly be proved for any given world. *) 
Theorem rN : (* = R5 *)
forall p : o, [ p ] -> [ L p ] .
intros. mv. L_i. apply H. Qed.

Theorem sK: (* = R6 *)
[ mforall p : o, mforall q : o,
(N (p m-> q)) m-> (N p) m-> (N q) ]. 
mv. intros p q H0 H1. N_i. 
N_e H0 H2. N_e H1 H3. auto. Qed.

Theorem rT : (* = DR1 *)
[ mforall p : o, (L p) m-> p ]. 
mv. intros p H. L_e H H0. auto.
apply r_reflexivity. Qed.

Theorem r4: 
[ mforall p : o, 
(L p) m-> (L (L p)) ]. 
mv. intros p H. L_i. L_i. 
apply H. apply r_transitivity with w0;
auto. Qed.

Theorem MT1 : 
[ mforall p : o, mforall q : o, 
( p m-> q ) m-> ( m~ q m-> m~ p ) ]. 
mv. intros p q H H0 H1. apply H0.
apply H. auto. Qed.
 
Theorem MT2 : 
[ mforall p : o, mforall q : o, 
(m~ p m-> m~ q ) m-> ( q m-> p ) ]. 
mv. intros p q H H0. apply NNPP.
intro. apply H; auto. Qed.

Theorem LMT : 
[ mforall p : o, mforall q : o, 
L ( p m-> q ) m-> L ( m~ q m-> m~ p ) ]. 
mv. intros p q H. L_i. apply MT1.
pose proof (H w0). auto. Qed.

Theorem NENA : 
[ mforall Q : u -> o, 
(m~ mexists x : u, m~ Q x) 
m-> mforall x : u, Q x ].
mv. intros Q H. intro. apply NNPP. intro. 
apply H. exists x. auto. Qed.

Theorem NAEN : 
[ mforall Q : u -> o, 
(m~ mforall x : u, Q x) 
m-> mexists x : u, m~ Q x ].
mv. intros Q H. apply NNPP. intro. 
apply H. apply NENA. auto. Qed.

Theorem ANNE : 
[ mforall Q : u -> o, 
(mforall x : u, m~ Q x) 
m-> m~ mexists x : u, Q x ].
mv. intros Q H. intro. destruct H0. 
apply (H x); auto. Qed.

Theorem NMNL : [ mforall p : o, 
(m~ (M (m~ p)) m-> (L p)) ]. 
mv. intros p H. L_i. apply NNPP. intro. 
apply H. M_i w0. apply H0. Qed.

Theorem NLNM : [ mforall p : o, 
(m~ (L (m~ p)) m-> (M p)) ]. 
mv. intros p. intro. apply NNPP.
intro. apply H. L_i. intro. apply H0. 
M_i w0. auto. Qed.

Theorem MNLN : [ mforall p : o, 
(M p) m-> m~ (L (m~ p)) ]. 
mv. intros p H C. M_e H.
pose proof (C w0 R). auto. Qed.

Theorem LNMN : [ mforall p : o, 
(L p) m-> m~ (M (m~ p)) ]. 
mv. intros p H C. M_e C. apply C.
L_e H H1. auto. Qed.

Theorem NLMN : [ mforall p : o, 
m~ (L p) m-> (M (m~ p)) ]. 
mv. intros p H. apply NNPP. intro.
apply H. apply NMNL. auto. Qed.

Theorem M_L_to_L: 
[ mforall p : o, (M (L p)) m-> (L p) ].
mv. intros p H. M_e H. apply rT.
L_i. L_i. L_e H H1. auto.
apply r_transitivity with w. 
apply r_symmetry; auto. 
apply r_transitivity with w1; auto. Qed.
(* Theorem M p -> L ( p -> L p ) -> L p. Used to prove P.11. 
Theorem P11L :
[ mforall p : o, (M p) m-> 
  L (p m-> L p) m-> L p ]. 
mv. intros p H0 H1. apply LMT in H1.
apply rK in H1. apply MT1 in H1.
apply M_L_to_L. apply NLNM. 
apply H1. apply MNLN. auto.
Qed.*)
Theorem rB : [ mforall p : o, 
p m-> (L (M p)) ]. 
mv. intros p H. L_i. 
apply r_symmetry in R. M_i w; auto.
Qed.

Lemma mp_M : 
[ mforall p : o, mforall q : o, 
(M p) m-> (L (p m-> q)) m-> (M q) ]. 
Proof. mv. intros p q H1 H2. M_e H1. 
M_i w0. L_e H2 H3. apply H3. exact H1. Qed.

Lemma not_M_L_not : 
[ mforall p : o, ( m~ (M p)) 
  m-> (L (m~ p))].
mv. intros p H. L_i. intro H2. apply H. M_i w0. exact H2. Qed.

Theorem mneq_sym : 
[ mforall x : u, mforall y : u, 
  x m<> y m-> y m<> x ].
mv. intros x y H0 H1. apply H0. auto. Qed.

(* *)
