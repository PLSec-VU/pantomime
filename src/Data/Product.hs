module Data.Product
  ( Product
  , type (>-)
  , nil
  , extend
  , retract
  , fetch
  ) where

import Control.Monad.ST (runST)
import Data.Kind (Type)
import Data.Member (type (>-) (..))
import Data.Primitive.SmallArray
  ( SmallArray
  , indexSmallArray
  , createSmallArray
  , thawSmallArray
  , unsafeFreezeSmallArray
  , sizeofSmallArray
  , resizeSmallMutableArray
  )
import GHC.Types (Any)
import Unsafe.Coerce (unsafeCoerce)

-- | A product of values for all the types in @ts@.
data Product (ts :: [Type]) where
  Product :: !(SmallArray Any) -> Product ts

-- | A unit 'Product' type.
nil :: Product '[]
nil = Product $ createSmallArray 0 undefined (const $ pure ()) 

-- | Extend a 'Product' type to contain the given value.
extend :: forall t ts. t -> Product ts -> Product (t : ts)
extend value (Product arr) = Product $ runST do
  let size = sizeofSmallArray arr
  arr' <- thawSmallArray arr 0 size
  let value' = unsafeCoerce @_ @Any value
  arr'' <- resizeSmallMutableArray arr' (size + 1) value'
  unsafeFreezeSmallArray arr''

-- | Remove an element from the 'Product' type.
retract :: forall t ts. Product (t : ts) -> Product ts
retract (Product arr) = Product $ runST do
  let size = sizeofSmallArray arr
  arr' <- thawSmallArray arr 0 size
  arr'' <- resizeSmallMutableArray arr' (size - 1) undefined
  unsafeFreezeSmallArray arr''

-- | Get an element from the 'Product' type.
fetch :: forall t ts. t >- ts => Product ts -> t
fetch (Product arr) = do
  let size = sizeofSmallArray arr
  let idx = size - 1 - reifyIndex @_ @t @ts
  let value = indexSmallArray arr idx
  unsafeCoerce value
