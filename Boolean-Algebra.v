Parameter Element : Type.

Parameter And : Element -> Element -> Element.
Parameter Or : Element -> Element -> Element.
Parameter Neg : Element -> Element.

Notation "x * y" := (And x y).
Notation "x + y" := (Or x y).
Notation "~ x" := (Neg x).

Parameter One : Element.
Parameter Zero : Element.

Axiom Commutativity_And : forall x y, x * y = y * x.
Axiom Commutativity_Or : forall x y, x + y = y + x.

Axiom Associativity_And : forall x y z, (x * y) * z = x * (y * z).
Axiom Associativity_Or : forall x y z, (x + y) + z = x + (y + z).

Axiom Identity_And : forall x, x * One = x.
Axiom Identity_Or : forall x, x + Zero = x.

Axiom Distributivity_And_over_Or : forall x y z, x * (y + z) = (x * y) + (x * z).
Axiom Distributivity_Or_over_And : forall x y z, x + (y * z) = (x + y) * (x + z).

Axiom Complement_And : forall x, x * (~ x) = Zero.
Axiom Complement_Or : forall x, x + (~ x) = One.

Axiom Uniqueness_of_Negation : forall x y, x * y = Zero -> x + y = One -> y = ~ x.

Require Import Setoid.

Theorem Indempotence_And : forall x, x * x = x.
Proof.
  intros x.
  rewrite <- (Identity_Or (x * x)).
  rewrite <- (Complement_And x).
  rewrite <- Distributivity_And_over_Or.
  rewrite -> Complement_Or.
  rewrite -> Identity_And.
  reflexivity.
Qed.

Theorem Boundary_Or : forall x, x + One = One.
Proof.
  intros x.
  rewrite <- (Identity_And (x + One)).
  rewrite <- (Complement_Or x) at 2.
  rewrite <- Distributivity_Or_over_And.
  rewrite -> Commutativity_And.
  rewrite -> Identity_And.
  rewrite -> Complement_Or.
  reflexivity.
Qed.

Theorem Double_Negation : forall x, (~ ~ x) = x.
Proof.
  intros x.
  rewrite <- (Uniqueness_of_Negation (~ x) x).
  reflexivity.
  rewrite -> Commutativity_And.
  rewrite -> Complement_And.
  reflexivity.
  rewrite -> Commutativity_Or.
  rewrite -> Complement_Or.
  reflexivity.
Qed.

Theorem Absorption_Or_And : forall x y, x + (x * y) = x.
Proof.
  intros x y.
  rewrite <- (Identity_And x) at 1.
  rewrite <- Distributivity_And_over_Or.
  rewrite -> Commutativity_Or.
  rewrite -> Boundary_Or.
  rewrite -> Identity_And.
  reflexivity.
Qed.