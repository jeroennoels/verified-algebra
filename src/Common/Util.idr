module Common.Util

import public Data.So
import public Data.Vect
import public Data.Rel
import public Decidable.Decidable
import public Common.Abbrev

%default total
%access public export

export
rewriteRelation : (rel : Binrel s) -> a = aa -> b = bb -> rel a b -> rel aa bb
rewriteRelation rel p q given = rewrite sym p in rewrite sym q in given

export
contraposition : (p -> q) -> Not q -> Not p
contraposition f contra p = contra (f p)

total export
butNotLeft : Either a b -> Not a -> b
butNotLeft (Left a) contra = absurd (contra a)
butNotLeft (Right b) _ = b

total
isItSo : (b : Bool) -> Dec (So b)
isItSo True = Yes Oh
isItSo False = No absurd


data EitherErased : Type -> Type -> Type where
  Left  : .a -> EitherErased a b
  Right : .b -> EitherErased a b


namespace Either3Erased
  data Either3Erased : Type -> Type -> Type -> Type where
    Left   : .a -> Either3Erased a b c
    Middle : .b -> Either3Erased a b c
    Right  : .c -> Either3Erased a b c

implementation Show (EitherErased a b) where
  show (Left _) = "Left"
  show (Right _) = "Right"

implementation Show (Either3Erased a b c) where
  show (Left _) = "Left"
  show (Middle _) = "Middle"
  show (Right _) = "Right"


decideBoth : (a -> b -> c) -> (c -> a) -> (c -> b) -> Dec a -> Dec b -> Dec c
decideBoth pair left right = dec
  where
    dec (Yes a) (Yes b) = Yes (pair a b)
    dec (No contra) _ = No (contra . left)
    dec _ (No contra) = No (contra . right)


||| Reduce code clutter: if you inline this where it is used, an
||| explicit type annotation would be needed.
decision : Decidable [s,s] rel => (a,b : s) -> Dec (rel a b)
decision {s} = decide {ts = [s,s]}
