module Instances.OrderZZ

import Data.Combinators
import Data.ZZ

%default total
%access public export

interface Bifunctor (f : Type -> Type -> Type) where
  bimap : (a -> b) -> (c -> d) -> f a c -> f b d

implementation Bifunctor Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right b) = Right (g b)

zzSucc : ZZ -> ZZ
zzSucc (Pos n) = Pos (S n)
zzSucc (NegS Z) = Pos Z
zzSucc (NegS (S n)) = NegS n

||| todo
partial
zzSuccPlus : (x,y : ZZ) -> plusZ (zzSucc x) y = zzSucc (plusZ x y)
zzSuccPlus (Pos n) (Pos m) = Refl


lteTotal : (n,m : Nat) -> Either (LTE n m) (LTE m n)
lteTotal Z _ = Left LTEZero
lteTotal _ Z = Right LTEZero
lteTotal (S n) (S m) = bimap LTESucc LTESucc (lteTotal n m)

lteAntisymmetric : LTE n m -> LTE m n -> n = m
lteAntisymmetric {n = Z} {m = Z} _ _ = Refl
lteAntisymmetric (LTESucc p) (LTESucc q) = cong $ lteAntisymmetric p q

LteZZ : ZZ -> ZZ -> Type
LteZZ (Pos n) (Pos m) = LTE n m
LteZZ (NegS n) (NegS m) = LTE m n
LteZZ (NegS _) (Pos _) = Unit
LteZZ (Pos _) (NegS _) = Void

zzLteRefl : (x : ZZ) -> LteZZ x x
zzLteRefl (Pos _) = lteRefl
zzLteRefl (NegS _) = lteRefl


zzLteTransitive : (x,y,z : ZZ) -> LteZZ x y -> LteZZ y z -> LteZZ x z
zzLteTransitive (Pos _)  (Pos _)  (Pos _)  p q = lteTransitive p q
zzLteTransitive (NegS _) (NegS _) (NegS _) p q = lteTransitive q p
zzLteTransitive (NegS _) _        (Pos _)  _ _ = MkUnit
zzLteTransitive (Pos _)  (NegS _) (NegS _) _ _ impossible
zzLteTransitive (Pos _)  (Pos _)  (NegS _) _ _ impossible

total
zzLteAntisymmetric : (x,y : ZZ) -> LteZZ x y -> LteZZ y x -> x = y
zzLteAntisymmetric (Pos n) (Pos m) p q = cong $ lteAntisymmetric p q
zzLteAntisymmetric (NegS n) (NegS m) p q = cong $ lteAntisymmetric q p

zzLteTotal : (x,y : ZZ) -> Either (LteZZ x y) (LteZZ y x)
zzLteTotal (Pos _) (NegS _) = Right ()
zzLteTotal (NegS _) (Pos _) = Left ()
zzLteTotal (Pos n) (Pos m) = lteTotal n m
zzLteTotal (NegS n) (NegS m) = lteTotal m n

total
zzLteSucc : (x,y : ZZ) -> LteZZ x y -> zzSucc x `LteZZ` zzSucc y
zzLteSucc (Pos _) (Pos _) prf = LTESucc prf
zzLteSucc (NegS (S _)) (NegS (S _)) prf = fromLteSucc prf
zzLteSucc (NegS (S _)) (NegS Z) _ = ()
zzLteSucc (NegS (S _)) (Pos _) _ = ()
zzLteSucc (NegS Z) (Pos _) _ = lteAddRight Z
zzLteSucc (NegS Z) (NegS Z) _ = lteRefl

isLteZZ : (x,y : ZZ) -> Dec (LteZZ x y)
isLteZZ (Pos n) (Pos m) = isLTE n m
isLteZZ (NegS n) (NegS m) = isLTE m n
isLteZZ (NegS _) (Pos _) = Yes ()
isLteZZ (Pos _) (NegS _) = No absurd
