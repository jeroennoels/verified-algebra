module Instances.OrderZZ

import public Data.Vect
import public Data.Rel
import public Decidable.Decidable
import Data.ZZ

%default total
%access export

||| LTE for ZZ, build on top of LTE for Nat.
public export
data LTEZ : ZZ -> ZZ -> Type where
  LtePosPos : LTE n m -> LTEZ (Pos n) (Pos m)
  LteNegNeg : LTE n m -> LTEZ (NegS m) (NegS n)
  LteNegPos : LTEZ (NegS _) (Pos _)

||| Because a positive number is always greater than a negative one.
public export
implementation Uninhabited (Pos _ `LTEZ` NegS _) where
  uninhabited _ impossible

public export
unwrapLtePosPos : LTEZ (Pos n) (Pos m) -> LTE n m
unwrapLtePosPos (LtePosPos prf) = prf

public export
unwrapLteNegNeg : LTEZ (NegS n) (NegS m) -> LTE m n
unwrapLteNegNeg (LteNegNeg prf) = prf


||| TODO. Consider import from Decidable.Order
lteAntisymmetric : LTE n m -> LTE m n -> n = m
lteAntisymmetric LTEZero LTEZero = Refl
lteAntisymmetric (LTESucc p) (LTESucc q) = cong $ lteAntisymmetric p q

||| Not yet in the base libraries.
public export
interface Bifunctor (f : Type -> Type -> Type) where
  bimap : (a -> b) -> (c -> d) -> f a c -> f b d

||| Not yet in the base libraries.
public export
implementation Bifunctor Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right b) = Right (g b)

||| TODO. Consider import from Decidable.Order
lteTotal : (n,m : Nat) -> Either (LTE n m) (LTE m n)
lteTotal Z _ = Left LTEZero
lteTotal _ Z = Right LTEZero
lteTotal (S n) (S m) = bimap LTESucc LTESucc (lteTotal n m)


lteReflZ : (x : ZZ) -> LTEZ x x
lteReflZ (Pos _) = LtePosPos lteRefl
lteReflZ (NegS _) = LteNegNeg lteRefl

lteTransitiveZ : (x,y,z : ZZ) -> LTEZ x y -> LTEZ y z -> LTEZ x z
lteTransitiveZ _ _ _ (LtePosPos p) (LtePosPos q) = LtePosPos (lteTransitive p q)
lteTransitiveZ _ _ _ (LteNegNeg p) (LteNegNeg q) = LteNegNeg (lteTransitive q p)
lteTransitiveZ _ _ _ (LteNegNeg _) LteNegPos = LteNegPos
lteTransitiveZ _ _ _ LteNegPos (LtePosPos _) = LteNegPos

lteAntisymmetricZ : (x,y : ZZ) -> LTEZ x y -> LTEZ y x -> x = y
lteAntisymmetricZ _ _ (LtePosPos p) (LtePosPos q) = cong $ lteAntisymmetric p q
lteAntisymmetricZ _ _ (LteNegNeg p) (LteNegNeg q) = cong $ lteAntisymmetric q p

lteTotalZ : (x,y : ZZ) -> Either (LTEZ x y) (LTEZ y x)
lteTotalZ (Pos _) (NegS _) = Right LteNegPos
lteTotalZ (NegS _) (Pos _) = Left LteNegPos
lteTotalZ (Pos n) (Pos m) = bimap LtePosPos LtePosPos (lteTotal n m)
lteTotalZ (NegS n) (NegS m) = bimap LteNegNeg LteNegNeg (lteTotal m n)

||| The difficulty here, is to hop over the split at zero.
lteSuccZ : (x,y : ZZ) -> LTEZ x y -> LTEZ (Pos 1 + x) (Pos 1 + y)
lteSuccZ _ _ (LtePosPos p) = LtePosPos (LTESucc p)
lteSuccZ (NegS (S _)) (NegS (S _)) (LteNegNeg p) = LteNegNeg (fromLteSucc p)
lteSuccZ (NegS (S _)) (NegS Z) _ = LteNegPos
lteSuccZ (NegS (S _)) (Pos _) _ = LteNegPos
lteSuccZ (NegS Z) (Pos _) _ = LtePosPos LTEZero
lteSuccZ (NegS Z) (NegS Z) _ = LtePosPos lteRefl
lteSuccZ (NegS Z) (NegS (S _)) (LteNegNeg _) impossible
lteSuccZ (Pos _) (NegS _) p = absurd p

||| The difficulty here, is to hop over the split at zero.
ltePredZ : (x,y : ZZ) -> LTEZ x y -> LTEZ (NegS Z + x) (NegS Z + y)
ltePredZ (Pos (S _)) (Pos (S _)) (LtePosPos p) = LtePosPos (fromLteSucc p)
ltePredZ (Pos Z) (Pos (S _)) _ = LteNegPos
ltePredZ (Pos Z) (Pos Z) _ = LteNegNeg lteRefl
ltePredZ (NegS _) (Pos (S _)) _ = LteNegPos
ltePredZ (NegS _) (Pos Z) _ = LteNegNeg LTEZero
ltePredZ (NegS n) (NegS m) (LteNegNeg p) = LteNegNeg (LTESucc p)
ltePredZ (Pos (S _)) (Pos Z) (LtePosPos _) impossible
ltePredZ (Pos _) (NegS _) p = absurd p

||| Lemma
private
lteLeftTranslationInvariantPosZ : (x,y : ZZ) -> (n : Nat) ->
  LTEZ x y -> LTEZ (Pos n + x) (Pos n + y)
lteLeftTranslationInvariantPosZ x y Z prf =
  rewrite plusZeroLeftNeutralZ x in
  rewrite plusZeroLeftNeutralZ y in prf
lteLeftTranslationInvariantPosZ x y (S n) prf =
  rewrite sym $ plusAssociativeZ (Pos 1) (Pos n) x in
  rewrite sym $ plusAssociativeZ (Pos 1) (Pos n) y in
  lteSuccZ _ _ (lteLeftTranslationInvariantPosZ x y n prf)

||| Lemma
private
lteLeftTranslationInvariantNegZ : (x,y : ZZ) -> (n : Nat) ->
  LTEZ x y -> LTEZ (NegS n + x) (NegS n + y)
lteLeftTranslationInvariantNegZ x y Z prf = ltePredZ x y prf
lteLeftTranslationInvariantNegZ x y (S n) prf =
  rewrite sym $ plusAssociativeZ (NegS Z) (NegS n) x in
  rewrite sym $ plusAssociativeZ (NegS Z) (NegS n) y in
  ltePredZ _ _ (lteLeftTranslationInvariantNegZ x y n prf)

||| This order is translation invariant.
lteLeftTranslationInvariantZ : (x,y,a : ZZ) ->
  LTEZ x y -> plusZ a x `LTEZ` plusZ a y
lteLeftTranslationInvariantZ x y (Pos n) =
  lteLeftTranslationInvariantPosZ x y n
lteLeftTranslationInvariantZ x y (NegS n) =
  lteLeftTranslationInvariantNegZ x y n

||| Make ZZ into a discrete ordered group.
lteDiscreteZ : (x : ZZ) ->
  Not (x = Pos Z) -> LTEZ x (Pos Z) -> LTEZ (Pos 1 + x) (Pos Z)
lteDiscreteZ (Pos (S _)) _ (LtePosPos p) = absurd (succNotLTEzero p)
lteDiscreteZ (Pos Z) notZ _ = absurd (notZ Refl)
lteDiscreteZ (NegS Z) _ LteNegPos = LtePosPos LTEZero
lteDiscreteZ (NegS (S _)) _ LteNegPos = LteNegPos

||| Lift a decision from Nat to ZZ.
public export
toLtePosPos : Dec (LTE n m) -> Dec (LTEZ (Pos n) (Pos m))
toLtePosPos (Yes prf) = Yes (LtePosPos prf)
toLtePosPos (No contra) = No (contra . unwrapLtePosPos)

||| Lift a decision from Nat to ZZ.
public export
toLteNegNeg : Dec (LTE n m) -> Dec (LTEZ (NegS m) (NegS n))
toLteNegNeg (Yes prf) = Yes (LteNegNeg prf)
toLteNegNeg (No contra) = No (contra . unwrapLteNegNeg)

public export
isLTEZ : (x,y : ZZ) -> Dec (LTEZ x y)
isLTEZ (Pos n) (Pos m) = toLtePosPos (isLTE n m)
isLTEZ (NegS n) (NegS m) = toLteNegNeg (isLTE m n)
isLTEZ (NegS _) (Pos _) = Yes LteNegPos
isLTEZ (Pos _) (NegS _) = No absurd

public export
implementation Decidable [ZZ, ZZ] LTEZ where
  decide = isLTEZ
