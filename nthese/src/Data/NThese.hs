{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Data.NThese (module Data.NThese) where

-- base
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Unsafe.Coerce (unsafeCoerce)

-- sop-core
import Data.SOP (All, AllN, AllZip, AllZipN, CollapseTo, HAp (..), HCollapse (..), HExpand (..), HSequence (..), HTrans, HTraverse_ (..), K (..), NP (..), NS (..), Prod, SList (..), SListI, hmap, sList, unK, type (-.->) (apFn), type (:.:) (..))
import Data.SOP.Classes (HPure (..), HTrans (..), Same)
import Data.SOP.Constraint (SListIN, Tail)

-- these
import Data.Functor.These (These1 (..))
import Data.These (These (..))
import Data.These qualified as These

-- semialign
import Data.Align (Align (..), Semialign (..), Unalign (..))

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
  -- | There is a value right here, and no values in the tail. Generalises 'This'.
  ThisHere ::
    -- | The value right here
    f a ->
    NThese f (a : as)
  -- | There is no value right here, but there are some values guaranteed to be in the tail. Generalises 'That'.
  ThatThere ::
    -- | The tail, guaranteed to contain values
    NThese f as ->
    NThese f (a : as)
  -- | The first present value is at the head, further values are in the tail. Generalises 'These'.
  TheseHere ::
    -- | The first present value
    f a ->
    -- | The tail, guaranteed to contain further values
    NThese f as ->
    NThese f (a : as)

-- * Accessing the head of 'NThese'

{- | Get the first element when it's guaranteed to be present

When there is only one type variable, 'TheseHere' is the only possible constructor,
so the type is isomorphic to @f a@.
-}
unThisHere :: NThese f '[a] -> f a
unThisHere (ThisHere fa) = fa
unThisHere (TheseHere _ impossible) = case impossible of {}
unThisHere (ThatThere impossible) = case impossible of {}

-- | Extract the first element, if present.
safeHead :: NThese f (a : as) -> Maybe (f a)
safeHead (ThisHere fa) = Just fa
safeHead (TheseHere fa _) = Just fa
safeHead (ThatThere _) = Nothing

-- | Prepend an element.
cons :: f a -> NThese f as -> NThese f (a : as)
cons = TheseHere

-- | Prepend a possibly absent element.
consMaybe :: Maybe (f a) -> NThese f as -> NThese f (a : as)
consMaybe = \case
  Nothing -> ThatThere
  Just fa -> cons fa

-- * Relationship to 'These'

-- | Extension of 'That' to more type parameters.
mkThat :: (SListI as) => f a2 -> NThese f (a1 : a2 : as)
mkThat fa2 = ThatThere $ ThisHere fa2

-- | Extension of 'These' to more type parameters.
mkThese :: (SListI as) => f a1 -> f a2 -> NThese f (a1 : a2 : as)
mkThese fa1 fa2 = TheseHere fa1 $ ThisHere fa2

-- | Witness that 'NThese' is a generalisation of 'These' with @n >= 2@ type variables.
fromThese :: (SListI as) => These (f a1) (f a2) -> NThese f (a1 : a2 : as)
fromThese = These.these ThisHere mkThat mkThese

-- | 'NThese' is recursively isomorphic to 'These'.
toThese :: NThese f (a : as) -> These (f a) (NThese f as)
toThese = \case
  ThisHere fa -> This fa
  ThatThere fas -> That fas
  TheseHere fa fas -> These fa fas

-- | Inverse of 'toThese'.
absorbThese :: (SListI as) => These (f a) (NThese f as) -> NThese f (a : as)
absorbThese = \case
  This fa -> ThisHere fa
  That fas -> ThatThere fas
  These fa fas -> TheseHere fa fas

-- * Interaction with other n-ary heterogeneous datatypes

-- ** N-ary sums

{- | Injection of n-ary sums.

An n-ary sum contains exactly one element, 'NThese' contains at least one element.
-}
fromNS :: (SListI as) => NS f as -> NThese f as
fromNS = \case
  Z fa -> ThisHere fa
  S ns -> ThatThere $ fromNS ns

-- | Project onto the first present element, discarding the rest.
headNS :: NThese f as -> NS f as
headNS = \case
  ThisHere fa -> Z fa
  ThatThere fas -> S $ headNS fas
  TheseHere fa _ -> Z fa

{- | Extract all elements into a 'NonEmpty' list.

The information that we have at most one element of each type is lost.
-}
toNSs :: (SListI as) => NThese f as -> NonEmpty (NS f as)
toNSs = \case
  ThisHere fa -> Z fa :| []
  ThatThere nt -> toNSs nt <&> S
  TheseHere fa fas -> Z fa `NonEmpty.cons` fmap S (toNSs fas)

-- ** N-ary products

{- | Injection of n-ary products.

An n-ary products contains exactly, n elements, 'NThese' contains at most one element.
-}
fromNP :: (SListI as) => NP f (a : as) -> NThese f (a : as)
fromNP = \case
  fa :* Nil -> ThisHere fa
  fa :* fas@(_ :* _) -> TheseHere fa $ fromNP fas

{- | Injection of possibly absent n-ary products.

@'NP' ('Maybe' :.: f) as@ contains 0 to n elements, 'NThese' contains at least one element.
In case that there is no element, 'Nothing' is returned.
-}
fromNPMaybe :: NP (Maybe :.: f) as -> Maybe (NThese f as)
fromNPMaybe = \case
  Nil -> Nothing
  Comp (Just fa) :* fas -> Just $ maybe (ThisHere fa) (TheseHere fa) $ fromNPMaybe fas
  Comp Nothing :* fas -> fromNPMaybe fas <&> ThatThere

{- | Projection onto possibly absent n-ary products.

The information that there is at least one element is lost.
-}
toNP :: (SListI as) => NThese f as -> NP (Maybe :.: f) as
toNP = \case
  ThisHere fa -> Comp (Just fa) :* hpure (Comp Nothing)
  ThatThere fas -> Comp Nothing :* toNP fas
  TheseHere fa fas -> Comp (Just fa) :* toNP fas

{- | Zip two 'NThese' together.

Each position may contain:

* No value, this is covered by the 'NThese' structure
* One or two values, this is represented in each 'These1' structure
-}
zipNThese :: (SListI as) => NThese f as -> NThese g as -> NThese (These1 f g) as
zipNThese = \case
  ThisHere fa -> \case
    ThisHere ga -> ThisHere $ These1 fa ga
    ThatThere gas -> TheseHere (This1 fa) $ hmap That1 gas
    TheseHere ga gas -> TheseHere (These1 fa ga) $ hmap That1 gas
  ThatThere fas -> \case
    ThisHere ga -> TheseHere (That1 ga) $ hmap This1 fas
    ThatThere gas -> ThatThere $ zipNThese fas gas
    TheseHere ga gas -> TheseHere (That1 ga) $ zipNThese fas gas
  TheseHere fa fas -> \case
    ThisHere ga -> TheseHere (These1 fa ga) $ hmap This1 fas
    ThatThere gas -> TheseHere (This1 fa) $ zipNThese fas gas
    TheseHere ga gas -> TheseHere (These1 fa ga) $ zipNThese fas gas

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
    Nothing -> ThisHere <$> fga
    Just fgas' ->
      align fga fgas' <&> \case
        This fga' -> ThisHere fga'
        That fgas'' -> ThatThere fgas''
        These fga' fgas'' -> TheseHere fga' fgas''
  where
    alignNP :: (SListI as, Semialign f) => NP (f :.: g) as -> Maybe (f (NThese g as))
    alignNP = \case
      Nil -> Nothing
      fgas -> case sList :: SList as of
        SCons -> Just $ alignN fgas

{- | Generalise 'nil' to 'NThese'.

Creates an 'NThese' filled with 'nil's.
-}
nilN :: forall a as f g. (SListI as, Align f) => NThese (f :.: g) (a : as)
nilN = hpure $ Comp nil

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

-- | Helper class to constrain the type level list on 'NThese' always to be nonempty
class (SListI as) => SListINThese as

type instance SListIN NThese = SListINThese

instance (SListI as, as ~ a : as') => SListINThese as

-- | Will incur an extra constraint on the type level list not to be empty
instance HPure NThese where
  hpure :: forall k (xs :: [k]) (f :: k -> Type). (SListIN NThese xs) => (forall (a :: k). f a) -> NThese f xs
  hpure fa = case sList :: SList xs of
    SNil -> error "Impossible pattern"
    SCons -> case sList :: SList (Tail xs) of
      SNil -> ThisHere fa
      SCons -> TheseHere fa $ hpure fa

  hcpure ::
    forall k (c :: k -> Constraint) (xs :: [k]) (proxy :: (k -> Constraint) -> Type) (f :: k -> Type).
    (AllN NThese c xs) =>
    proxy c ->
    (forall (a :: k). (c a) => f a) ->
    NThese f xs
  hcpure proxy fa = case sList :: SList xs of
    SNil -> error "Impossible pattern"
    SCons -> case sList :: SList (Tail xs) of
      SNil -> ThisHere fa
      SCons -> TheseHere fa $ hcpure proxy fa

instance HAp NThese where
  hap = \case
    Nil -> \case {}
    fna :* fnas -> \case
      ThisHere fa -> ThisHere $ apFn fna fa
      ThatThere gas -> ThatThere $ hap fnas gas
      TheseHere fa fas -> TheseHere (apFn fna fa) $ hap fnas fas

type instance CollapseTo NThese a = NonEmpty a

instance HCollapse NThese where
  hcollapse = collapse_NThese
    where
      collapse_NThese :: (SListI as) => NThese (K a) as -> NonEmpty a
      collapse_NThese = \case
        ThisHere fa -> NonEmpty.singleton $ unK fa
        ThatThere fas -> collapse_NThese fas
        TheseHere (K fa) fas -> fa `NonEmpty.cons` collapse_NThese fas

type instance AllN NThese c = All c

instance HTraverse_ NThese where
  htraverse_ ::
    forall k (xs :: [k]) (g :: Type -> Type) (f :: k -> Type).
    (SListIN NThese xs, Applicative g) =>
    (forall (a :: k). f a -> g ()) ->
    NThese f xs ->
    g ()
  htraverse_ f = htraverse_0
    where
      htraverse_0 :: (Applicative g) => NThese f as -> g ()
      htraverse_0 = \case
        ThisHere fa -> f fa
        ThatThere fas -> htraverse_0 fas
        TheseHere fa fas -> f fa *> htraverse_0 fas

  hctraverse_ ::
    forall k (c :: k -> Constraint) (xs :: [k]) (g :: Type -> Type) (proxy :: (k -> Constraint) -> Type) (f :: k -> Type).
    (AllN NThese c xs, Applicative g) =>
    proxy c ->
    (forall (a :: k). (c a) => f a -> g ()) ->
    NThese f xs ->
    g ()
  hctraverse_ _ f = hctraverse_0
    where
      hctraverse_0 :: (AllN NThese c as, Applicative g) => NThese f as -> g ()
      hctraverse_0 = \case
        ThisHere fa -> f fa
        ThatThere fas -> hctraverse_0 fas
        TheseHere fa fas -> f fa *> hctraverse_0 fas

instance HSequence NThese where
  hsequence' = hsequence'0
    where
      hsequence'0 :: (Applicative f) => NThese (f :.: g) as -> f (NThese g as)
      hsequence'0 = \case
        ThisHere (Comp fga) -> ThisHere <$> fga
        ThatThere fgas -> ThatThere <$> hsequence'0 fgas
        TheseHere (Comp fga) fgas -> TheseHere <$> fga <*> hsequence'0 fgas

  hctraverse' ::
    forall k (c :: k -> Constraint) (xs :: [k]) (g :: Type -> Type) (proxy :: (k -> Constraint) -> Type) (f :: k -> Type) (f' :: k -> Type).
    (AllN NThese c xs, Applicative g) =>
    proxy c ->
    (forall (a :: k). (c a) => f a -> g (f' a)) ->
    NThese f xs ->
    g (NThese f' xs)
  hctraverse' _ f = hctraverse'0
    where
      hctraverse'0 :: (AllN NThese c as) => NThese f as -> g (NThese f' as)
      hctraverse'0 = \case
        ThisHere fa -> ThisHere <$> f fa
        ThatThere fas -> ThatThere <$> hctraverse'0 fas
        TheseHere fa fas -> TheseHere <$> f fa <*> hctraverse'0 fas

  htraverse' ::
    forall k (xs :: [k]) (g :: Type -> Type) (f :: k -> Type) (f' :: k -> Type).
    (SListIN NThese xs, Applicative g) =>
    (forall (a :: k). f a -> g (f' a)) ->
    NThese f xs ->
    g (NThese f' xs)
  htraverse' f = htraverse'0
    where
      htraverse'0 :: NThese f as -> g (NThese f' as)
      htraverse'0 = \case
        ThisHere fa -> ThisHere <$> f fa
        ThatThere fas -> ThatThere <$> htraverse'0 fas
        TheseHere fa fas -> TheseHere <$> f fa <*> htraverse'0 fas

instance HExpand NThese where
  hexpand fa0 = \case
    ThisHere fa -> fa :* hpure fa0
    ThatThere fas -> fa0 :* hexpand fa0 fas
    TheseHere fa fas -> fa :* hexpand fa0 fas
  hcexpand proxy fa0 = \case
    ThisHere fa -> fa :* hcpure proxy fa0
    ThatThere fas -> fa0 :* hcexpand proxy fa0 fas
    TheseHere fa fas -> fa :* hcexpand proxy fa0 fas

type instance AllZipN NThese c = AllZip c

instance HTrans NThese NThese where
  htrans proxy f = \case
    ThisHere fa -> ThisHere $ f fa
    ThatThere fas -> ThatThere $ htrans proxy f fas
    TheseHere fa fas -> TheseHere (f fa) $ htrans proxy f fas

  hcoerce = unsafeCoerce
