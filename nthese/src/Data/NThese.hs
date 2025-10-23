module Data.NThese (module Data.NThese) where

-- base
import Data.Foldable (traverse_)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (fromMaybe)
import Unsafe.Coerce (unsafeCoerce)

-- sop-core
import Data.SOP (All, AllN, AllZip, AllZipN, CollapseTo, HAp (..), HApInjs (hapInjs), HCollapse (..), HExpand (..), HSequence (..), HTrans, HTraverse_ (..), K (..), NP (..), NS (..), Prod, SList (..), SListI, hcliftA, hliftA, hmap, hzipWith, sList, unComp, unK, type (-.->) (Fn, apFn), type (:.:) (..))
import Data.SOP.Classes (HPure (..), HTrans (..), Same)
import Data.SOP.Constraint (SListIN)

-- these
import Data.Functor.These (These1 (..))
import Data.These (These (..))
import Data.These qualified as These

-- witherable
import Witherable (Filterable (catMaybes), (<&?>))

-- semialign
import Data.Align (Semialign (..), Unalign (..))

{- | An n-ary generalisation of the 'These' datatype.

@'NThese' f [a1, a2, a3, ...]@ contains at least one of @f a1@, @f a2@, and so on,
and potentially all of them.

@'NThese' 'Identity' [a, b]@ is isomorphic to @'These' a b@.

= Relations to other types

* @'NP' f as@ is the n-ary product. It contains exactly @n@ elements. There is an injection from 'NP' into 'NThese' with all positions filled, but in general 'NThese' needn't fill every position.
* @'NP' ('Maybe' :.: f) as@ can contain 0 to @n@ elements, whereas 'NThese' always contains at least one element.
* @'NS' f as@ is the n-ary sum. It contains exacty 1 element. There is an injection from 'NS' into 'NThese', but in general 'NThese' can fill more positions.
* @'NonEmpty' a@ is the nonempty homogeneous list. It is similar to @'NThese' ('K' a) as@, but 'NonEmpty' can contain 1 to infinitely many elements,
  while 'NThese' has at most @n@ elements and contains positional information about the present values.
-}
data NThese :: (k -> Type) -> [k] -> Type where
  -- | The first present value is at the head, further values may be present in the tail.
  TheseHere ::
    -- | The first present value
    f a ->
    -- | The tail, possibly containing values
    NP (Maybe :.: f) as ->
    NThese f (a : as)
  -- | There is no value right here, but there are some values guaranteed to be in the tail
  Those ::
    -- | The tail, guaranteed to contain values
    NThese f as ->
    NThese f (a : as)

-- * Accessing the head of 'NThese'

{- | Destruct the 'TheseHere' constructor.

When there is only one type variable, 'TheseHere' is the only possible constructor,
so the type is isomorphic to @f a@.
-}
unTheseHere :: NThese f '[a] -> f a
unTheseHere (TheseHere fa Nil) = fa
unTheseHere (Those impossible) = case impossible of {}

-- | Extract the first element, if present.
safeHead :: NThese f (a : as) -> Maybe (f a)
safeHead (TheseHere fa _) = Just fa
safeHead (Those _) = Nothing

-- | Prepend an element.
cons :: f a -> NThese f as -> NThese f (a : as)
cons fa fas = TheseHere fa $ toNP fas

-- | Prepend a possibly absent element.
consMaybe :: Maybe (f a) -> NThese f as -> NThese f (a : as)
consMaybe = \case
  Nothing -> Those
  Just fa -> cons fa

-- * Generalisation of 'These'

-- | Generalisation of 'This'.
mkThis :: (SListI as) => f a -> NThese f (a : as)
mkThis fa = TheseHere fa $ hpure $ Comp Nothing

-- | Generalisation of 'That'.
mkThat :: (SListI as) => f a2 -> NThese f (a1 : a2 : as)
mkThat fa2 = Those $ mkThis fa2

-- | Generalisation of 'These'.
mkThese :: (SListI as) => f a1 -> f a2 -> NThese f (a1 : a2 : as)
mkThese fa1 fa2 = TheseHere fa1 $ toNP $ mkThis fa2

-- | Witness that 'NThese' is a generalisation of 'These' with @n >= 2@ type variables.
fromThese :: (SListI as) => These (f a1) (f a2) -> NThese f (a1 : a2 : as)
fromThese = These.these mkThis mkThat mkThese

-- | 'NThese' is recursively isomorphic to 'These'.
toThese :: NThese f (a : as) -> These (f a) (NThese f as)
toThese = \case
  TheseHere fa fas -> case fromNPMaybe fas of
    Nothing -> This fa
    Just fas' -> These fa fas'
  Those fas -> That fas

-- | Inverse of 'toThese'.
absorbThese :: (SListI as) => These (f a) (NThese f as) -> NThese f (a : as)
absorbThese = \case
  This fa -> mkThis fa
  That fas -> Those fas
  These fa fas -> cons fa fas

-- * Interaction with other n-ary heterogeneous datatypes

-- ** N-ary sums

{- | Injection of n-ary sums.

An n-ary sum contains exactly one element, 'NThese' contains at least one element.
-}
fromNS :: (SListI as) => NS f as -> NThese f as
fromNS = \case
  Z fa -> mkThis fa
  S ns -> Those $ fromNS ns

-- | Project onto the first present element, discarding the rest.
headNS :: NThese f as -> NS f as
headNS = \case
  TheseHere fa _ -> Z fa
  Those fas -> S $ headNS fas

{- | Extract all elements into a 'NonEmpty' list.

The information that we have at most one element of each type is lost.
-}
toNSs :: (SListI as) => NThese f as -> NonEmpty (NS f as)
toNSs = \case
  TheseHere fa np -> Z fa :| (np & hapInjs <&?> htraverse' unComp <&> S)
  Those nt -> toNSs nt <&> S

-- ** N-ary products

{- | Injection of n-ary products.

An n-ary products contains exactly, n elements, 'NThese' contains at most one element.
-}
fromNP :: (SListI as) => NP f (a : as) -> NThese f (a : as)
fromNP = \case
  fa :* fas -> TheseHere fa $ hmap (Comp . Just) fas

{- | Injection of possibly absent n-ary products.

@'NP' ('Maybe' :.: f) as@ contains 0 to n elements, 'NThese' contains at least one element.
In case that there is no element, 'Nothing' is returned.
-}
fromNPMaybe :: NP (Maybe :.: f) as -> Maybe (NThese f as)
fromNPMaybe = \case
  Nil -> Nothing
  Comp (Just fa) :* fas -> Just $ TheseHere fa fas
  Comp Nothing :* fas -> fromNPMaybe fas <&> Those

{- | Projection onto possibly absent n-ary products.

The information that there is at least one element is lost.
-}
toNP :: NThese f as -> NP (Maybe :.: f) as
toNP = \case
  TheseHere fa fas -> Comp (Just fa) :* fas
  Those fas -> Comp Nothing :* toNP fas

{- | Zip two 'NThese' together.

Each position may contain:

* No value, this is covered by the 'NThese' structure
* One or two values, this is represented in each 'These1' structure
-}
zipNThese :: (SListI as) => NThese f as -> NThese g as -> NThese (These1 f g) as
zipNThese = \case
  TheseHere fa1 fas1 -> \case
    TheseHere fa2 fas2 ->
      TheseHere (These1 fa1 fa2) $
        hzipWith
          ( \case
              (Comp (Just fa1')) -> \case
                (Comp (Just fa2')) -> Comp $ Just $ These1 fa1' fa2'
                (Comp Nothing) -> Comp $ Just $ This1 fa1'
              (Comp Nothing) -> \case
                (Comp (Just fa2')) -> Comp $ Just $ That1 fa2'
                (Comp Nothing) -> Comp Nothing
          )
          fas1
          fas2
    Those fas2 -> TheseHere (This1 fa1) $ toNP $ hzipWith (\(Comp fa1') fa2 -> maybe (That1 fa2) (`These1` fa2) fa1') fas1 fas2
  Those fas1 -> \case
    TheseHere fa2 fas2 -> TheseHere (That1 fa2) $ toNP $ hzipWith (\(Comp fa2') fa1 -> maybe (This1 fa1) (These1 fa1) fa2') fas2 fas1
    Those fas2 -> Those $ zipNThese fas1 fas2

-- * Generalisation of type classes related to 'These'

{- | Generalise 'align' to 'NThese'.

'align' has this type signature:

@
'align' :: Semialign f => f a -> f b -> f ('These' a b)
@

This generalises zipping 2 @f@-structures, and requiring that at each @f@-position we have either an @a@ or a @b@.

'alignN' generalises this in two directions:

1. Incidental: We use nested @f (g a)@-structures. (But @g@ can always be set to identity, and is thus irrelevant.)
1. Crucial: We have @n@ values instead of 2. At each @f@-position we can have 1 to n values.
-}
alignN :: forall a as f g. (SListI as, Semialign f) => NP (f :.: g) (a : as) -> f (NThese g (a : as))
alignN = \case
  Comp fga :* fgas -> case alignNP fgas of
    Nothing -> mkThis <$> fga
    Just fgas' ->
      align fga fgas' <&> \case
        This fga' -> mkThis fga'
        That fgas'' -> Those fgas''
        These fga' fgas'' -> TheseHere fga' $ toNP fgas''
  where
    alignNP :: (SListI as, Semialign f) => NP (f :.: g) as -> Maybe (f (NThese g as))
    alignNP = \case
      Nil -> Nothing
      fgas -> case sList :: SList as of
        SCons -> Just $ alignN fgas

{- | Generalise 'unalign' to 'NThese'.

'unalign' has this type signature:

@
unalign :: Unalign f => f (These a b) -> (f a, f b)
@

Similar to 'alignN' we generalise this from 2 values to @n@ values.
-}
unalignN :: forall f g as. (Unalign f, SListI as) => f (NThese g as) -> NP (f :.: g) as
unalignN fgas = case sList :: SList as of
  SNil -> Nil
  SCons ->
    fgas
      & unalignWith toThese
      & \(fga, fgas') -> Comp fga :* unalignN fgas'

type instance Same NThese = NThese

type instance Prod NThese = NP

instance HAp NThese where
  hap = \case
    Nil -> \case {}
    fna :* fnas -> \case
      TheseHere fa fas -> TheseHere (apFn fna fa) $ helper fnas fas
      Those gas -> Those $ hap fnas gas
    where
      helper :: NP (f -.-> g) as -> NP (Maybe :.: f) as -> NP (Maybe :.: g) as
      helper = \case
        Nil -> \case
          Nil -> Nil
        Fn fna :* fnas -> \case
          Comp fa :* fas -> Comp (fna <$> fa) :* helper fnas fas

type instance CollapseTo NThese a = NonEmpty a

type instance SListIN NThese = SListI

instance HCollapse NThese where
  hcollapse = collapse_NTHese
    where
      collapse_NTHese :: (SListI as) => NThese (K a) as -> NonEmpty a
      collapse_NTHese = \case
        TheseHere (K fa) fas -> fa :| (fas & hmap (maybe (K Nothing) (K . Just . unK) . unComp) & hcollapse & catMaybes)
        Those fas -> collapse_NTHese fas

type instance AllN NThese c = All c

instance HTraverse_ NThese where
  htraverse_ f = \case
    TheseHere fa fas -> f fa *> htraverse_ (traverse_ f . unComp) fas
    Those fas -> htraverse_ f fas
  hctraverse_ proxy f = \case
    TheseHere fa fas -> f fa *> hctraverse_ proxy (traverse_ f . unComp) fas
    Those fas -> hctraverse_ proxy f fas

instance HSequence NThese where
  hsequence' = \case
    TheseHere (Comp fga) fgas -> TheseHere <$> fga <*> htraverse' (fmap Comp . traverse unComp . unComp) fgas
    Those fgas -> Those <$> hsequence' fgas

  hctraverse' proxy f = \case
    TheseHere fa fas -> TheseHere <$> f fa <*> hctraverse' proxy (fmap Comp . traverse f . unComp) fas
    Those fas -> Those <$> hctraverse' proxy f fas

  htraverse' f = \case
    TheseHere fa fas -> TheseHere <$> f fa <*> htraverse' (fmap Comp . traverse f . unComp) fas
    Those fas -> Those <$> htraverse' f fas

instance HExpand NThese where
  hexpand fa0 = \case
    TheseHere fa fas -> fa :* hliftA (fromMaybe fa0 . unComp) fas
    Those fas -> fa0 :* hexpand fa0 fas
  hcexpand proxy fa0 = \case
    TheseHere fa fas -> fa :* hcliftA proxy (fromMaybe fa0 . unComp) fas
    Those fas -> fa0 :* hcexpand proxy fa0 fas

type instance AllZipN NThese c = AllZip c

instance HTrans NThese NThese where
  htrans proxy f = \case
    TheseHere fa fas -> TheseHere (f fa) $ htrans proxy (Comp . fmap f . unComp) fas
    Those fas -> Those $ htrans proxy f fas

  hcoerce = unsafeCoerce
