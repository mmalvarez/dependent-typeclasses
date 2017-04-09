Check (1 + 1).
Inductive ABC :=
| A | B | C : ABC.

Check ABC_ind.

Lemma foo : A = B -> False.
Proof.
  intro H; inversion H.
Qed.
  
Class Functor (T : Type -> Type) : Type :=
  {fmap : forall {X Y : Type}, (X -> Y) -> T X -> T Y;
   _ : forall {X : Type} (x : T X), fmap (fun x => x) x = x;
   _ : forall {X Y Z : Type} (f : X -> Y) (g : Y -> Z) (x : T X),
              fmap g (fmap f x) = fmap (fun x => g (f x)) x
  }.


(* Dependent functors.
   Pack an index type with a dependent type *)
(*Record Pack (I : Type) :=
  {
    Fam1 : I -> Type;
    Fam2 : forall (i : I), Fam1 i -> Type
  }.
 *)
Record Pack (I : Type) (T : I -> Type) : Type :=
  MkPack { Fam : forall (i : I), T i -> Type }.

Inductive PackM (I I' : Type) (T : I -> Type) (T' : I' -> Type) :=
  MkPackM { f1 : I' -> I;
            f2 : forall (i' : I'), T (f1 i') -> T' i'
          }
.
(* IDEA: "dependent indexed functors" *)
(* Question: how to get out all the "extraneous" type parameters?
   Does the functor instance apply just to the Packing structure
   (i.e., not the type?) *)


Print MkPackM.

Definition PackM_Id (I : Type) (T : I -> Type) : PackM I I T T :=
  {| f1 := (fun (i : I) => i); f2 := (fun i t => t)|}.


(* Q: Do we quantify over _all_ Packs ? *)
(* Q: what are the correctness axioms? *)
Class DFunctor (I : Type) (T : I -> Type) (*(P : Pack I T)*) :=
  {
    dfmap :
      forall {I' T'}, PackM I I' T T' -> Pack I T -> Pack I' T';
    _ : dfmap (PackM_Id I T) = fun (x : Pack I T) => x;
  }.

Check @dfmap.


    _ : forall {I' T' I'' T''}
          (f : PackM I I' T T') (g : PackM I' I'' T' T''),
        fun (x : Pack I T) =>
      dfmap f (dfmap g x) = dfmap (fun k => g (f k)) x
  }.




(* do we also need I -> I'? *)
Inductive PackM (I I' : Type) :=
  {
    F1 : Pack I -> Pack I';
  }

  }.
    F1 : I' -> I;
    F2 : forall (i : I), F1 i' -> F1
  }


Class DFunctor {I : Type} (P : Pack I) :=


Definition Identity : Type -> Type := @id Type.
Instance FunIdentity : Functor Identity :=
  { fmap := fun X Y f => f }.
Proof.
  reflexivity.
  reflexivity.
Qed.

Class Dual (F G : Type -> Type) : Type :=
  {zap : forall (X Y Z : Type),
      (X -> Y -> Z) ->
      F X -> G Y -> Z }.

Definition zonk {F G : Type -> Type} {DFG : Dual F G} {A B : Type} : F (A -> B) -> G A -> B :=
  zap (A -> B) A B (fun x => x).

Instance DIdId : Dual Identity Identity :=
  {zap := fun X Y Z f a b => f a b}.

Inductive FProd (F G : Type -> Type) (A : Type) : Type :=
   Prod : (F A) -> (G A) -> FProd F G A.

Inductive FSum (F G : Type -> Type) (A : Type) : Type :=
  Inl : (F A) -> FSum F G A
| Inr : (G A) -> FSum F G A.

Check @fmap.

Instance FunFProd {F G : Type -> Type}
         {FunF : Functor F} {FunG : Functor G} : Functor (FProd F G)
  :=
  {fmap := fun X Y f x =>
             match x with
             | Prod _ _ _ fa ga => Prod _ _ _ (@fmap) (@fmap)
             end
  }.