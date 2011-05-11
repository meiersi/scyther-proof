-- | Extensions to the interface of 'Data.Map'.
module Extension.Data.Map (
    module Data.Map
  , adjustWithDefault
  , queryMap
  , invertMap
) where

import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Data.Map

-- | Adjusts a value at a specific key. When the key is not a member of the map,
-- the given default value is inserted at this key and adjusted.
adjustWithDefault :: Ord k => a -> (a -> a) -> k -> Map k a -> Map k a
adjustWithDefault e f = alter (maybe (Just . f $ e) (Just . f))

-- | Compute some query over the value of the map at a specific key, while
-- defaulting to a fixed value, if there is no value to query
queryMap :: Ord k => (a -> b) -> b -> k -> Map k a -> b
queryMap f e k = maybe e f . Data.Map.lookup k

-- | Invert a map.
invertMap :: Ord v => M.Map k v -> M.Map v k
invertMap = M.fromList . map (uncurry $ flip (,)) . M.toList
