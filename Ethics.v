(** Verification of Spinoza's proof of the existence of God from the _Ethics_, using Charles Jarrett's formalization from _The Logical Structure of Spinoza's Ethics_ (http://www.jstor.org/stable/20115250). The bimodal logic used in the proofs is implemented separately in the [ML.v] library. *)

Require Import Classical.
Require Import ML.

(* *)

(** * Predicates *) 

(* *)

(** [ At x ] := x is an attribute. *)

Variable At : u -> o. 

(** [ Fr x ] := x is free. *)

Variable Fr : u -> o. 

(** [ De x ] := x is (an instance of) desire. *)

Variable De : u -> o. 

(** [ Et x ] := x is eternal. *)

Variable Et : u -> o. 

(** [ Fn x ] := x is finite. *)

Variable Fn : u -> o. 

(** [ Gd x ] := x is a god. *)

Variable Gd : u -> o. 

(** [ Lv x ] := x is (an instance of) love. *)

Variable Lv : u -> o. 

(** [ Id x ] := x is an idea. *)

Variable Id : u -> o. 

(** [ Mo x ] := x is a mode. *)

Variable Mo : u -> o. 

(** [ Su x ] := x is a substance. *)

Variable Su : u -> o. 

(** [ Tr x ] := x is true. *)

Variable Tr : u -> o. 

(** [ It x ] := x is an intellect. *)

Variable It : u -> o. 

(** [ Wl x ] := x is a will. *)

Variable Wl : u -> o. 

(** [ AO x y ] := x is an attribute of y. *)

Variable AO : u -> u -> o. 

(** [ Cv x y ] := x is conceived through y.    *)

Variable Cv : u -> u -> o. 

(** [ Ag x y ] := x agrees with y. *)

Variable Ag : u -> u -> o. 

(** [ In x y ] := x is in y. *)

Variable In : u -> u -> o. 

(** [ Ca x y ] := x is a cause of y. *)

Variable Ca : u -> u -> o. 

(** [ Lm x y ] := x limits y. *)

Variable Lm : u -> u -> o. 

(** [ MO x y ] := x is a mode of y. *)

Variable MO : u -> u -> o. 

(** [ OO x y ] := x is an object of y. *)

Variable OO : u -> u -> o. 

(** [ Pw x y ] := x is the power of y. *)

Variable Pw : u -> u -> o. 

(** [ MR x y ] := x has more reality than y. *)

Variable MR : u -> u -> o. 

(** [ MA x y ] := x has more attributes than y. *)

Variable MA : u -> u -> o. 

(** [ CT x y z ] := x is common to y and z. *)

Variable CT : u -> u -> u -> o. 

(* *)

(** * Definitions *) 

(* *)

(** I. By that which is self—caused, I mean that of which the essence involves existence, or that of which the nature is only conceivable as existent. *)

Axiom D1 : 
[ mforall x : u, ( Ca x x m/\ m~ (mexists y : u, y m<> x m/\ Ca y x) )
m<-> L (mexists y : u, y m= x) ].

(** II. A thing is called finite after its kind, when it can be limited by another thing of the same nature; for instance, a body is called finite because we always conceive another greater body. So, also, a thought is limited by another thought, but a body is not limited by thought, nor a thought by body. *)

Axiom D2 : [ mforall x : u, Fn x
m<-> mexists y : u, y m<> x m/\ Lm y x 
m/\ mforall z : u, AO z x m<-> AO z y ].

(** III. By substance, I mean that which is in itself, and is conceived through itself: in other words, that of which a conception can be formed independently of any other conception. *)

Axiom D3 : [ mforall x : u, 
Su x m<-> In x x m/\ Cv x x ].

(** IV. By attribute, I mean that which the intellect perceives as constituting the essence of substance. *)

Axiom D4a : [ mforall x : u, At x 
m<-> mexists y : u, ( Su y m/\ In x y 
m/\ Cv x y m/\ In y x m/\ Cv y x ) ]. 

Axiom D4b : [ mforall x : u, mforall y : u,
AO x y m<-> ( At x m/\ Cv y x ) ].

(** V. By mode, I mean the modifications of substance, or that which exists in, and is conceived through, something other than itself. *)

Axiom D5a : [ mforall x : u, mforall y : u,
MO x y m<-> ( x m<> y m/\ In x y  m/\ Cv x y ) ].

Axiom D5b : [ mforall x : u, 
Mo x m<-> mexists y : u, Su y m/\ MO x y ].

(** VI. By God, I mean a being absolutely infinite—that is, a substance consisting in infinite attributes, of which each expresses eternal and infinite essentiality. *)

Axiom D6 : [ mforall x : u, 
Gd x m<-> (Su x m/\ mforall y : u, At y m-> AO y x) ].

(** VII. That thing is called free, which exists solely by the necessity of its own nature, and of which the action is determined by itself alone. On the other hand, that thing is necessary, or rather constrained, which is determined by something external to itself to a fixed and definite method of existence or action. *)

Axiom D7 : 
[ mforall x : u, mforall y : u, 
In x y m<-> ( ( x m<> y 
m-> L ( ( mexists v : u, v m= x ) 
m-> ( mexists v : u, v m= y ) ) ) 
m/\ ( ( x m= y ) m-> ( m~ mexists z : u, 
 z m<> x m/\ L ( ( mexists v : u, v m= x )
m-> ( mexists v : u, v m= z ) ) ) ) ) ].

(** VIII. By eternity, I mean existence itself, in so far as it is conceived necessarily to follow solely from the definition of that which is eternal. *)

Axiom D8 : [ mforall x : u, 
Et x m<-> L ( mexists y : u, y m= x ) ]. 

(* *)

(** * Axioms *) 

(* *)

(** I. Everything which exists, exists either in itself or in something else. *)

Axiom A1 : 	
[ mforall x : u, In x x m\/ mexists y : u, y m<> x m/\ In x y ].

(** II. That which cannot be conceived through anything else must be conceived through itself. *)

Axiom A2 : [ mforall x : u, 
( m~ mexists y : u, x m<> y m/\ Cv x y ) m<-> Cv x x ].

(** III. From a given definite cause an effect necessarily follows; and, on the other hand, if no definite cause be granted, it is impossible that an effect can follow. *)

Axiom A3 : [ mforall x : u,
mforall y : u, Ca y x 
m-> N ( ( mexists u : u, u m= y ) 
m<-> ( mexists u, u m= x ) ) ].

(** IV. The knowledge of an effect depends on and involves the knowledge of a cause.*)

Axiom A4 : [ mforall x : u,
mforall y : u, Ca x y m<-> Cv y x ].

(** V. Things which have nothing in common cannot be understood, the one by means of the other; the conception of one does not involve the conception of the other. *)

Axiom A5 : [ mforall x : u,
mforall y : u, m~ ( mexists z : u, 
CT z x y ) m<-> m~ Cv x y m/\ m~ Cv y x ].

(** VI. A true idea must correspond with its ideate or object. *)

Axiom A6 : [ mforall x : u, Id x
m-> ( Tr x m<-> mexists y : u, 
OO y x m/\ Ag x y ) ].

(** VII. If a thing can be conceived as non—existing, its essence does not involve existence. *)

Axiom A7 : [ mforall x : u,
M ( m~ mexists y : u, y m= x )  
m<-> m~ L ( mexists y : u, y m= x ) ].

(** Axioms 8-13, 18 are suppressed premises from Jarrett's formalization. *)

Axiom A8 : [ mforall x : u,
mforall y : u, In x y m-> Cv x y ].

Axiom A9 : [ mforall x : u, 
mexists y : u, AO y x ]. 

Axiom A10 : [ mforall x : u,
mforall y : u, Su x m/\ Su y 
m-> MR x y m-> MA x y ].

Axiom A11 : [ mforall x : u, 
mforall y : u, Su x m-> Lm y x m-> Su y ].

Axiom A12 : [ mforall x : u, 
( mexists y : u, MO x y ) m-> Mo x ].

Axiom A13 : 
[ M ( mexists x : u, Gd x) ].

Axiom A18 : 
[ mforall x : u, mforall y : u,
Su x m-> Su y m-> MR x y m-> MA x y ].

(* *)

(** * Derived Premises *)

(* *)

Theorem DP1 : 
[ mforall x : u, Su x m<-> In x x ].
mv. intro. split. apply D3. intro.
apply D3. split. auto. apply A8.
auto. Qed.

Theorem DP2 : 
[ mforall x : u, Cv x x m-> In x x ].
mv. do 2 intro. pose proof (A1 w x).
inversion H0. auto. apply A2 in H.
exfalso. apply H. inversion H1.
exists x0. inversion H2. split; auto.
intro. apply H3. auto.
apply A8. auto. Qed.

Theorem DP3 : 
[ mforall x : u, Su x m-> At x ].
mv. intros x H. apply D4a. exists x. 
split. auto. 
split. apply D3. auto. 
split. apply A8. apply D3. auto. 
apply D3. auto. Qed.

Theorem DP4 : 
[ mforall x : u, Su x m<-> Cv x x ].
intro. split. apply D3. intro.
apply D3. split; auto. apply DP2. auto.
Qed.

Theorem DP5 : 
[ mforall x : u, Su x m\/ Mo x ].
mv. intro. pose proof (A1 w x). destruct H.
left. apply DP1. auto.
right. inversion H. destruct H0.
pose proof (A8 w x x0 H1). apply A12. 
exists x0. apply D5a. split. 
apply mneq_sym. auto. split; auto.
Qed.

Theorem DP6 : [ mforall x : u, 
m~ ( Su x m/\ Mo x ) ].
mv. do 2 intro. destruct H. 
apply D3 in H. destruct H.
apply A2 in H1. apply H1.
apply D5b in H0. inversion H0.
exists x0. destruct H2. 
apply D5a in H3. destruct H3. 
destruct H4. split; auto. Qed.

Theorem DP7 : 
[ mforall x : u, mforall y : u, 
AO x y m-> Su y m-> x m= y ].
mv. intros x y H H0. apply D3 in H0. 
apply D4b in H. apply NNPP. intro. 
destruct H. destruct H0. apply A2 in H3.
apply H3. exists x. split; auto. intro. 
apply H1. unfold mequal. auto. Qed.

(** Derived premises I-III are my additions. *)

Theorem DPI : 
[ mforall x : u, (Su x m/\ m~ Mo x) 
  m\/ (m~ Su x m/\ Mo x) ].
mv. intro x. (pose proof DP5 w x). 
(pose proof DP6 w x). simpl in *.
destruct H; [ left | right ]; split; auto;
intro; apply H0; auto; split; auto. Qed.

Theorem DPII : 
[ mforall x : u, Su x m-> AO x x ].
mv. intros x. pose proof (A9 w x). 
inversion H. pose proof (DP7 w x0 x H0). 
intro. apply H1 in H2. unfold mequal in H2.
subst. auto. Qed.

Hint Resolve DPII.

Theorem DPIII : 
[ mforall x : u, Su x m<-> Ca x x ].
mv. intros. split; intro. apply A4. 
apply DP4. auto. apply DP4. apply A4. 
auto. Qed.

(** We also prove some simple tauotologies for proof simplication. *)

Theorem modus_tollens : forall P Q : Prop,
( P -> Q ) <-> ( ~ Q -> ~ P ).
do 2 intro. split. do 3 intro. 
apply H0. auto. do 2 intro. apply NNPP.
intro. apply H; auto. Qed.

Theorem iff_neg : forall P Q : Prop,
( P <-> Q ) <-> ( ~ P <-> ~ Q).
intros. split; intro; destruct H; split; 
apply modus_tollens; auto. Qed.

Theorem ineq_sym : forall {X : Type} 
(x y : X), x <> y -> y <> x.
do 5 intro. apply H. symmetry. auto. Qed. 

(* *)

(** * Propositions *) 

(* *)

(** I. Substance is by nature prior to its modifications. *)

Theorem P1 : 
[ mforall x : u, mforall y : u, MO x y 
m-> Su y m-> ( In x y m/\ In y y ) ].
mv. intros. split. apply D5a in H. 
inversion H. inversion H2. auto.
apply D3 in H0. inversion H0. auto.
Qed.

(** II. Two substances, whose attributes are different, have nothing in common. *)

Lemma P2L : [ mforall x : u, mforall y : u,
Su x m-> x m<> y m-> m~ Cv x y ].
mv. do 5 intro. apply (A2 w x). 
apply D3. auto. exists x0; split; auto.
Qed.

Theorem P2 : [ mforall x : u, 
mforall y : u, Su x m-> Su y m-> x m<> y 
m-> m~ mexists z : u, CT z x y ].
mv. intros x y H0 H1 H2. apply (A5 w). 
split; apply P2L; auto. apply mneq_sym.
auto. Qed.
 
(** III. Things which have nothing in common cannot be one the cause of the other. *)

Theorem P3 : 
[ mforall x : u, mforall y : u, 
( m~ mexists z : u, CT z x y ) 
m-> ( m~ Ca x y m/\ m~ Ca y x ) ].
mv. intros. split; intro; apply A4 in H0;
apply A5 in H; inversion H; auto.
Qed.

(** IV. Two or more distinct things are distinguished one from the other, either by the difference of the attributes of the substances, or by the difference of their modifications. *)

Theorem P4 : 
[ mforall x : u, mforall y : u, 
x m<> y m-> mexists z : u, mexists z' : u, 
( ( AO z x m/\ AO z' y m/\ z m<> z' ) 
m\/ ( AO z x m/\ ( z m= x ) m/\ Mo y )
m\/ ( AO z' y m/\ ( z' m= y ) m/\ Mo x ) 
m\/ ( Mo x m/\ Mo y ) ) ]. 
mv. intros x y H. pose proof (DPI w x). 
pose proof (DPI w y). simpl in *. 
do 2 destruct H0; do 2 destruct H1;
exists x; exists y. left. 
split; try split; try apply DPII; auto.
right. left. 
split; try split; try apply DPII; auto.
unfold mequal. auto.
right. right. left. 
split; try split; try apply DPII; auto.
unfold mequal. auto.
right. right. right. 
split; try split; try apply DPII; auto.
Qed.

(** V. There cannot exist in the universe two or more substances having the same nature or attribute. *)

Theorem P5 : 
[ mforall x : u, mforall y : u, 
Su x m-> Su y m-> x m<> y 
m-> m~ mexists w, AO w x m/\ AO w y ].
mv. intros x y H0 H1 H2 H3. 
inversion H3 as [ z ]. destruct H.
pose proof (DP7 w z x H H0).
pose proof (DP7 w z y H4 H1).
unfold mequal in *.
apply H2. subst. auto. Qed.

(** VI. One substance cannot be produced by another substance. *)

Theorem P6 : 
[ mforall x : u, mforall y : u, 
Su x m-> Su y m-> x m<> y 
m-> m~ Ca x y m/\ m~ Ca y x ].
mv. do 5 intro. apply P3. apply P2; 
auto. Qed.

Theorem P6c: [ mforall x : u, Su x m-> 
m~ mexists y : u, y m<> x m/\ Ca y x ].
do 4 intro. apply DP4 in H. 
apply A2 in H. apply H. do 2 destruct H0.
exists x0. split. apply ineq_sym. auto. apply (A4 w). auto. Qed.

(** VII. Existence belongs to the nature of substances. *)

Theorem P7 : [ mforall x : u,
Su x m-> L ( mexists y : u, y m= x ) ].
mv. do 2 intro. apply D1. split. 
apply DPIII. auto. apply P6c. auto. Qed. 

(** VIII. Every substance is necessarily infinite. *)

Theorem P8 : 
[ mforall x : u, Su x m-> m~ Fn x ].
mv. do 3 intro. apply D2 in H0. 
do 2 destruct H0. destruct H1.
apply A11 in H1; auto. 
apply ineq_sym in H0.
pose proof (P5 w x x0 H H1 H0).
apply H3. pose proof (A9 w x). 
inversion H4. exists x1. split; auto.
apply H2. auto. Qed.

(** IX. The more reality or being a thing has, the greater the number of its attributes (Def. iv.). *)

Theorem P9 : 
[ mforall x : u, mforall y : u,
Su x m-> Su y m-> MR x y m-> MA x y ].
apply A18. Qed.

(** X. Each particular attribute of the one substance must be conceived through itself. *)

Theorem P10 : 
[ mforall x : u, At x m-> Cv x x ].
mv. do 2 intro. apply D4a in H.
do 2 destruct H. destruct H0. destruct H1.
destruct H2. apply DP4 in H. 
assert (x = x0). apply NNPP. intro.
apply A2 in H. apply H. exists x.
split; try apply ineq_sym ; auto. 
subst. auto. Qed.

(** XI. God, or substance, consisting of infinite attributes, of which each expresses eternal and infinite essentiality, necessarily exists. *)

Lemma P11L0 : [ mforall x : u, 
L ( ( L ( mexists y, y m= x ) ) m-> Su x ) ].
mv. intros x. apply rN. mv. intro. 
apply D1 in H. destruct H. apply A4 in H.
apply DP4; auto. Qed.

Lemma P11L1 :
[ mforall x : u, Su x m-> L (Su x) ].
mv. intros x H. apply P7 in H. 
apply (r4 w) in H. 
pose proof ( P11L0 w x). simpl in H0.
apply rK in H0. apply H0; auto. Qed.

Lemma P11L2 : 
[ mforall x : u, mforall y : u,
m~ ( x m<> y m/\ In x x m/\ In y y ) ].
mv. intros x y H. 
destruct H. destruct H0.
assert ( ( m~ mexists z : u, 
 z m<> x m/\ L ( ( mexists v : u, v m= x )
m-> ( mexists v : u, v m= z ) ) ) w ).
apply (D7 w x x); auto. unfold mequal;
auto. apply H2. exists y. split; 
try apply ineq_sym; auto. L_i. 
intro. apply (P7 w0). apply (P11L1 w); 
try apply DP1; auto. apply r_reflexivity.
Qed.

Lemma P11L3 :
[ mforall x : u, Su x m-> m~ ( L ( Gd x ) )
m-> M (mexists y : u, At y m/\ m~ AO y x) ].
mv. intros x H0 H1. apply NLMN in H1.
M_e H1. pose proof (D6 w0 x). simpl in H.  
apply iff_neg in H. apply H in H1.
M_i w0. apply NNPP. intro. apply H1.
split. pose proof (P11L1 w x H0).
apply H3; auto. intros y H3.
apply NNPP. intro. apply H2.
exists y; split; auto. Qed.

Lemma P11L4 : 
[ mforall x : u, Su x 
m-> M (mexists y : u, At y m/\ m~ AO y x) 
m-> M ( mexists x0 : u, mexists y0 : u,
x0 m<> y0 m/\ In x0 x0 m/\ In y0 y0 ) ].
mv. intros x H0 H1. M_e H1. M_i w0.
destruct H1 as [ z ] . destruct H.
pose proof (D4a w0 z). simpl in H2.
pose proof (D4b w0 z x). simpl in H3.
apply iff_neg in H3. destruct H2. 
clear H4. pose proof (H2 H). clear H2.
destruct H4 as [ y ]. exists x. exists y.
split. intro. apply H3 in H1. apply H1. 
split; auto. subst. destruct H2.
destruct H4. destruct H5. destruct H6.
auto. split; apply DP1. 
apply (P11L1 w); auto.
destruct H2. auto. Qed.

Lemma P11L5 :
[ mforall x : u, Su x m-> L (Gd x) ].
mv. intros x H. apply NNPP. intro C.
pose proof (P11L3 w x H C).
pose proof (P11L4 w x H H0).
M_e H1. do 2 destruct H1. 
pose proof P11L2. apply rN in H2. 
pose proof (H2 w w0 R x0 x1). apply H3.
auto. Qed.

Lemma P11L6 :
[ mforall x : u, Gd x m-> L (Gd x) ].
mv. intros x H. apply P11L5. apply D6. 
auto. Qed.

Lemma P11L7 :
[ L ((mexists x : u, Gd x) 
m-> L (mexists x : u, Gd x)) ].
mv. L_i. intro. destruct H.
assert (Su x w0). apply D6; auto.
exists x. pose proof (P11L6 w0 x H w1).
apply H2. auto. Qed.

Theorem P11 : [ L (mexists x : u, Gd x) ]. 
mv. apply P11L. apply A13. apply P11L7. Qed.

(* *)
