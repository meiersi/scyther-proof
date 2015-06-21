-- | Simple table representation. This module is meant to be imported qualified.
module Data.Table (
  -- * Datatypes
    Alignment(..)
  , Table

  -- ** Queries
  , toList
  , alignments
  , defaultAlignment
  , columns
  , rows

  -- ** Construction/Modification
  , empty
  , fromList
  , newRow
  , setAlignment
  , appendCell
  , appendNumCell

  -- ** Cell based access
  , getCell
  , setCell
  , headerLastCell
  , alignLastCell

  -- ** Pretty Printing
  , toLaTeX
) where

import Safe
import Data.List
import qualified Data.IntMap as IM

import Extension.Prelude

------------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------------

-- | Round a number to the given amount of decimals.
roundDecimal :: RealFrac a
             => Int  -- ^ Number of decimals after the decimal point
             -> a -> a
roundDecimal d n = fromIntegral ((round (multiplier * n))::Integer) / multiplier
  where
  multiplier :: RealFrac a => a
  multiplier = 10 ^^ d

-- | The maximum key of an 'IntMap', if there is one.
maxKey :: IM.IntMap a -> Maybe Int
maxKey = fmap (fst.fst) . IM.maxViewWithKey

-- | The minimal length of an array indexable by indices from '0' to 'maxKey'.
denseLength :: IM.IntMap a -> Int
denseLength = maybe 0 succ . maxKey

-- | Convert the sparse intmap to a dense list, filling the gaps with the given
-- default element.
toDenseList :: a -> IM.IntMap a -> [a]
toDenseList def m = case maxKey m of
  Just k  -> merge [0..k] (IM.toList m)
  Nothing -> []
  where
  merge [] vs = map snd vs
  merge ks [] = replicate (length ks) def
  merge ks@(k:ks') vs@((idx,v):vs') = case compare k idx of
    LT -> def : merge ks' vs
    EQ -> v   : merge ks' vs'
    GT -> v   : merge ks  vs'

-- | Convert a dense list to an 'IntMap' assuming the list has consecutive
-- indexes starting from '0'.
fromDenseList :: [a] -> IM.IntMap a
fromDenseList = IM.fromList . zip [0..]

------------------------------------------------------------------------------
-- Table datatype
------------------------------------------------------------------------------

type Cells a = IM.IntMap (IM.IntMap a)

-- | A column alignment.
data Alignment = AlignLeft | AlignRight
  deriving( Eq, Ord, Show )

-- | A table with aligned rows.
data Table a = Table {
    alignments :: IM.IntMap Alignment  -- ^ The alignment for each column
  , headers    :: IM.IntMap a          -- ^ The headers for each column
  , getCells   :: Cells a              -- ^ Cells indexed first by rows then by columns
  }
  deriving( Eq, Ord, Show )

instance Functor Table where
  fmap f = mapCellsAndHeaders (IM.map (IM.map f)) (IM.map f)

------------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------------

-- | The default alignment to be used for a row.
defaultAlignment :: Alignment
defaultAlignment = AlignLeft

-- | The number of columns of the table.
columns :: Table a -> Int
columns = maximumDef 0 . map (denseLength . snd) . IM.toList . getCells

-- | The number of rows of the table.
rows :: Table a -> Int
rows = denseLength . getCells

-- | Retrieve the contents of a cell if it exists.
getCell :: (Int,Int) -> Table a -> Maybe a
getCell (rowIdx, colIdx) = (IM.lookup colIdx =<<) . IM.lookup rowIdx . getCells

-- | View the index and the contents of the last cell.
viewLastCell :: Table a -> Maybe ((Int, Int), a)
viewLastCell t = do
  ((rowIdx,row),  _) <- IM.maxViewWithKey $ getCells t
  ((colIdx,cell), _) <- IM.maxViewWithKey $ row
  return ((rowIdx, colIdx), cell)

-- | Retrieve the index of the last cell.
lastCellIndex :: Table a -> Maybe (Int, Int)
lastCellIndex = fmap fst . viewLastCell

toList :: a -> Table a -> [[a]]
toList def = map (toDenseList def) . toDenseList IM.empty . getCells

------------------------------------------------------------------------------
-- Table construction
------------------------------------------------------------------------------

-- Internal helper functions
----------------------------

-- | Updtate the alignments.
mapAlignments :: (IM.IntMap Alignment -> IM.IntMap Alignment) -> Table a -> Table a
mapAlignments f t = t { alignments = f (alignments t) }

-- | Updtate the headers.
mapHeaders :: (IM.IntMap a -> IM.IntMap a) -> Table a -> Table a
mapHeaders f = mapCellsAndHeaders id f

-- | Update the cells.
mapCells :: (Cells a -> Cells a) -> Table a -> Table a
mapCells f = mapCellsAndHeaders f id

-- | Updtate the headers and the cells
mapCellsAndHeaders :: (Cells a -> Cells b)
                   -> (IM.IntMap a -> IM.IntMap b)
                   -> Table a -> Table b
mapCellsAndHeaders fCells fHeaders t =
  t { headers = fHeaders (headers t), getCells = fCells (getCells t) }


-- Externally available functions
---------------------------------

-- | Emtpy table.
empty :: Table a
empty = Table IM.empty IM.empty IM.empty

-- | Convert a list of rows to a table.
fromList :: [[a]] -> Table a
fromList = Table IM.empty IM.empty . fromDenseList . map fromDenseList

-- | Set the alignment of the given column.
setAlignment :: Int -> Alignment -> Table a -> Table a
setAlignment colIdx alignment = mapAlignments (IM.insert colIdx alignment)

-- | Set the header of the given column.
setHeader :: Int -> a -> Table a -> Table a
setHeader colIdx header = mapHeaders (IM.insert colIdx header)

-- | Set the contents of a cell.
setCell :: (Int,Int) -> a -> Table a -> Table a
setCell idx@(rowIdx, colIdx) x
  | rowIdx < 0 || colIdx < 0 = error $ "setCell: index out of range" ++ show idx
  | otherwise                = mapCells (IM.alter changeRow rowIdx)
  where
  changeRow Nothing    = Just $ IM.singleton colIdx x
  changeRow (Just row) = Just $ IM.insert colIdx x row

-- | Add a new empty row to the table.
newRow :: Table a -> Table a
newRow = mapCells $ \cells -> case maxKey cells of
  Just rowIdx -> IM.insert (succ rowIdx) IM.empty cells
  Nothing     -> IM.singleton 0 IM.empty

-- | Append a cell at the end of the last row
appendCell :: a -> Table a -> Table a
appendCell cell = mapCells $ \cells ->
  case IM.maxViewWithKey cells of
    Just ((rowIdx,row),cellsNoRow) ->
      case maxKey row of
        Just colIdx -> IM.insert rowIdx (IM.insert (succ colIdx) cell row) cellsNoRow
        Nothing     -> IM.insert rowIdx (IM.singleton 0 cell)              cellsNoRow
    Nothing -> IM.singleton 0 (IM.singleton 0 cell)

-- | Set the alignemnt of the last cell.
alignLastCell :: Alignment -> Table a -> Table a
alignLastCell al t = case lastCellIndex t of
  Just (_, colIdx) -> setAlignment colIdx al t
  Nothing          ->                        t

headerLastCell :: a -> Table a -> Table a
headerLastCell header t = case lastCellIndex t of
  Just (_, colIdx) -> setHeader colIdx header t
  Nothing          ->                         t

-- | Append a cell containing a number; i.e. round and right align.
appendNumCell :: (Show a, RealFrac a )
              => Int -- ^ Number of digits after the decimal point
              -> a -> Table String -> Table String
appendNumCell dec x =
  alignLastCell AlignRight . appendCell (show $ roundDecimal dec x)


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

type Aligner a =  Int  -- ^ The length to achieve.
               -> [a]  -- ^ The current list.
               -> [a]  -- ^ The aligned list.

-- | Align the number of elements in each list using the given alignment function.
alignBy :: Aligner a -> [[a]] -> [[a]]
alignBy _      [] = []
alignBy expand rs = map (expand maxLength) rs
  where
  maxLength = maximum $ map length rs

-- | Align the contents of each cell using the given aligment for each row.
alignCellsBy :: [Aligner a] -> [[[a]]] -> [[[a]]]
alignCellsBy expanders =
  transpose . zipWith alignBy (cycle expanders) . transpose . alignBy (flushLeftBy [[]])

-- | Convert a table to the body of a LaTeX table.
toLaTeX :: (a -> String) -> Table a -> String
toLaTeX toStr t =
  formatLines . map formatLine . alignCells . addHeaders . toList "" . fmap toStr $ t
  where
  addHeaders
    | IM.null $ headers t = id
    | otherwise           = ((toDenseList "" . IM.map toStr $ headers t):)
  doAlign AlignLeft  = flushLeft
  doAlign AlignRight = flushRight
  aligns = toDenseList defaultAlignment (alignments t) ++ repeat defaultAlignment
  alignCells = alignCellsBy (map doAlign aligns)
  formatLine = (++"\\\\") . concat . intersperse " & "
  formatLines = unlines


------------------------------------------------------------------------------
-- Some (manual) testing
------------------------------------------------------------------------------

{-
test = fromList $ [["simon","where","a"],["new","","world"],[],["order"]]
test1 = setHeader 1 "URGH" .setHeader 1 "WORDL" . appendNumCell 2 10.2 . alignLastCell AlignRight . appendCell "w" $ test

latex = putStrLn . toLaTeX id
-}
