module Extension.Data.Accessor (
  -- * Containers
  mapDirect
) where

import qualified Data.Map as M

import Data.Accessor
import Data.Accessor.Container

-- | A direct accessor for maps. Will fail at runtime, if the element is not
-- present.
mapDirect :: Ord k => k -> Accessor (M.Map k v) v
mapDirect k = accessor (M.! k) (\v -> M.insert k v)

