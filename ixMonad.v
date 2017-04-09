(* Here is an implementation of a dependent version of Kmett's indexed monads *)

(* First, the non-dependent version. We skip Applicative. *)
(* For "join" version of the Monad laws, see
https://en.wikipedia.org/wiki/Monad_(functional_programming)#fmap_and_join
 *)

Definition idn {A : Type} : A -> A := fun (a : A) => a.
Axiom funex :
  forall {A : Type} {B : A -> Type} (f g : forall (a : A), B a),
    (forall (a : A), f a = g a) -> f = g.

Definition comp {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun (a : A) => g (f a).

Lemma test : (fun x => x + 1)%nat = fun x => idn x + 1.
  apply funex.
  reflexivity.
Qed.

Class ixFunctor (F : Type -> Type -> Type -> Type) :=
  { imap : forall {A J K B : Type}, (A -> B) -> F A J K -> F B J K;
    _ : forall {A J K : Type}, @imap A J K A idn = idn;
    _ : forall {A B C J K : Type} (g : B -> C) (f : A -> B),
        @imap A J K C (comp g f) = comp (imap g) (imap f)}.

(* Q: should ifF be inside the struct, or an index as it is now? *)
Class ixPointed (F : Type -> Type -> Type -> Type) {ifF : ixFunctor F} :=
  { ireturn : forall {A I : Type}, A -> F A I I;
    _ : forall {A J B : Type} (f : A -> B), comp (@imap F ifF A J J B f) (ireturn) = comp ireturn f
  }.

Class ixMonad (F : Type -> Type -> Type -> Type) {ifF : ixFunctor F} {ipF : ixPointed F} :=
  { ibind : forall {J K L A B : Type},
      (F A J K) -> (A -> F B K L) -> F B J L;
    _ : forall {J K A B : Type} (f : A -> F B J K) (a : A),
        ibind (ireturn a) f = f a;
    _ : forall {J K A : Type} (m : F A J K),
        ibind m ireturn = m;
    _ : forall {J K L A B : Type} (f : A -> F B J K) (a : A),
        ibind (@ireturn F ifF ipF A J a) f = f a
  }.


(* A digression: depenent contents *)
(* a first attempt at a Pack type that is indexed. *)
(*Record Pack (I : Type) (F : I -> Type) : Type := MkPack {K : forall (i : I), F i}.*)

(* Bod corresponds to pointedness? *)
(*Record Pack : Type :=
  MkPack {Idx : Type; Fam : Idx -> Type; Bod : forall (i : Idx), Fam i}.*)

Record Pack : Type :=
  MkPack {Idx : Type; Fam : Idx -> Type}.

(* TODO: co or contravariant presheaves? *)
Record PackMorph (P1 P2 : Pack) : Type :=
  MkMorph { ixf : P1.(Idx) -> P2.(Idx)
            ; famf : forall (i : P1.(Idx)), P2.(Fam) (ixf i) -> P1.(Fam) i}.

(* "custom typechecking" for packs *)
(* TODO: how are these going to be indexed? *)
Record Edata (P : Pack) :=
  MkE { ei : P.(Idx); ef : P.(Fam) ei }.
Record Udata (P : Pack) :=
  MkU {uf : forall (i : P.(Idx)), P.(Fam) i}.

(* How to talk about instances of these pack types?
   That is, we need a new "typechecking" relation to describe how things can
   "be instances of" a Pack *)
(* There are 4 ways to be instances of this: all pairs drawn from {exists, forall}
   meaning we can have exists or forall for the index, as well as the family *)Check ei.

(* Why isn't this working? *)
Definition PackMorphDe {P1 P2 : Pack}
           (m : PackMorph P1 P2) (d : Edata P1) : Edata P2 :=
  {| ei := (ixf _ _ m (ei P1 d))
   ; ef := (famf _ _ m ei (ei  ))|}.
                                                           



(* Digression over. *)
(* OK, now for the dependent versions *)
(* Q: 2 or 3 parameters?
   First we will do the 3 parameter version for consistency with Kmett
 *)

Class dxFunctor (F : forall (A B : Type) (C : B -> Type), Type) :=
  { idmap : forall {A A' B : Type} {C : B -> Type}, (A -> A') -> F A B C -> F A' B C;
    _ : forall {}
          (* idmap idn = idn *)
          (* idmap const = const (?) *)
          (* idmap comp g f = comp (idmap g) (idmap f) *)
  }.

(*Q: how does join/bind work here? Something something coherence *)

Class dxPointed (F : forall (A B : Type) (C : B -> Type), Type) :=
  { idreturn : forall {A B},
      A -> F A B (fun _ => B) (* should this be id or const? *)
  }.

(* What order do the arrows compose? Outer then inner, or inner then outer?
   Maybe for this one you can have either work because the arrows do not
   depend on the value... ? *)

(* The first argument of the inner one! *)
Class dxMonad (F : forall (A B : Type) (C : B -> Type), Type) :=
  { idjoin : forall { },
      F (F A K L) J K -> F A J L }.



(* Now we have a 3 parameter "more dependent" functor, where
   the arrows can depend on the value type...
 *)

(* TODO: 2 parameter one, assuming it's even meaningful *)