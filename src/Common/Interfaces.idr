module Common.Interfaces

%default total
%access public export

interface AdditiveGroup s where
  (+) : s -> s -> s
  Neg : s -> s
  Zero : s
  
interface Unital s where  
  One : s
