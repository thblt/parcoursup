module Main where

import Data.List (sort, transpose, tails)
import Data.Maybe (fromJust)
import Data.Monoid (Sum (..), Product)
import qualified Data.Map as M
import qualified Data.Set as S

data Formation = Formation { fId :: IdFormation
                           , capacite :: Int
                           , fAdmis :: [Proposition] }
  deriving (Eq, Read, Show)

type Candidat = Char
type IdFormation = Int
type Proposition = (Candidat, Int)

type Parcoursup = [Formation]

-- * Calcul des affectations

-- ** Première méthode: éliminer les vœux de préférence inférieure au meilleur vœu admis

-- | Algorithme trivial: pour chaque candidat, supprime les vœux dont
-- la préférence est inférieur au vœu admis de préférence la plus
-- haute.  C'est ce que fait le Parcoursup ordinaire: les candidats
-- peuvent renoncer à des vœux, et (j'imagine) le font quand ils sont
-- admis sur un vœu qu'ils préfèrent.
simplifier :: Parcoursup -> Parcoursup
simplifier = stabilise simplifier1

-- | Une étape de `simplifier`
simplifier1 :: Parcoursup -> Parcoursup
simplifier1 fs = fmap (\x -> x { fAdmis = filter f (fAdmis x) }) fs
  where
    f (c, p) = p <= M.findWithDefault 1000 c meilleurs
    meilleurs = meilleurAdmis fs

-- | Autre stratégie d'élimination, chercher à fermer des listes
-- d'attente.  Une formation peut être close quand aucun des candidats
-- admis n'a d'autres vœux en liste d'attente après `simplifier` ---
-- cad que cette formation est sa favorite de celle qui ne l'ont pas
-- refusée.
fermer :: Parcoursup -> Parcoursup
fermer = stabilise fermer1

-- @TODO `fermer` devrait être du type Parcoursup -> (Parcoursup, Parcoursup) pour permettre d'afficher les listes d'admission.

fermer1 :: Parcoursup -> Parcoursup
fermer1 p = filter flt p
  where
    flt (Formation _ cap adm) = any (\(cand, pref) -> M.findWithDefault 1000 cand meilleurs /= pref) (take cap adm)
    meilleurs = meilleur p

-- | Simplifier et fermer constituent, ensemble, la première phase du
-- traitement.
phase1 = stabilise (simplifier . fermer)

-- ** Méthode d'optimisation par cycles

-- Il est possible que `simplifier` suffise à créer une situation où
-- plus aucun candidat n'est sur liste d'attente, cad que chacun a
-- zéro ou une admission.  C'est le cas optimal.  Dans ce scénario, le
-- vœu sur lequel chaque candidat est admis est son vœu de préférence
-- la plus élevée sur lequel il n'a pas été éliminé.
--
-- Mais il est aussi possible que `phase1` s'arrête en laissant des
-- candidatures en liste d'attente de préférence plus haute à une
-- candidature admise.
--
-- Dans certains cas, la situation n'a pas de solution, mais elle peut
-- en avoir, cad qu'il est possible de trouver des séries de
-- candidatures dont la suppression augmente le taux de satisfaction,
-- cad réduise le nb de candidatures en liste d'attente.
--
-- Pour faire ça, on cherche des *cycles*, cad à construire des
-- sous-ensembles des formations qui vérifient les propriétés suivantes:
--
-- - Un ensemble non-nul de candidatures non résolues,
--
-- - Émanant d'un ensemble déterminé de candidats tels qu'ils
-- - apparaissent tous au moins deux fois.
-- - Ces deux apparitions sont en ordre inverse
--
-- Pb qui va se poser: choisir parmi les cycles.

-- | Recherche de cycles
cycles :: Parcoursup -> (Parcoursup, [Candidat])
cycles p = undefined

type Paire = (Candidat, Candidat)
data FPaires = FPaires IdFormation Int [Paire]
  deriving (Eq, Show)

paires :: Parcoursup -> [FPaires]
paires p= fmap trans p
  where
    trans (Formation i c a) = FPaires i c (go a)
    go :: [Proposition] -> [(Candidat, Candidat)]
    go a = toPairs . filter (\cand -> cand `elem` cands) $ fmap fst a
    cands = doublons p

toPairs :: [a] -> [(a, a)]
toPairs l = [(x,y) | (x:ys) <- tails l, y <- ys]

-- | Identifier les candidats qui apparaissent deux fois.
doublons :: Parcoursup -> [Candidat]
doublons p = let
  tous = sort $ foldr ((++) . fmap fst . fAdmis) [] p
  ff :: Candidat -> (Maybe Candidat, S.Set Candidat) -> (Maybe Candidat, S.Set Candidat)
  ff c (Nothing, s) = (Just c, S.insert c s)
  ff c (Just c', s) | c /= c' = (Just c, s)
                    | otherwise = (Just c, S.insert c' s)
  in
    S.toList . snd $ foldr ff (Nothing, S.empty) tous

-- | On a besoin d'une fonction qui compare deux états de Parcoursup.
-- La comparaison peut renvoyer deux valeurs: soit un gain ou une
-- perte, exprimée comme un nombre entier (Just g), soit Nothing si la
-- seconde possibilite n'est pas acceptable.  Le gain ou la perte se
-- calcule selon, pour chaque candidat, la différence entre le rang de
-- son vœu admis dans ses préférences entre le premier et le
-- second. Si, par exemple, un candidat passe du second au premier
-- vœu, le gain est de 1, si deux candidats. Ça suppose que les rangs
-- aient été normalisés (avec `normaliser`) préalablement, sinon la
-- comparaison prendre en compte les rangs absolus des vœux, alors
-- qu'elle n'a de sens que relativement (si un candidat passe de 15°
-- au 1er vœu, mais qu'il a été éliminé des vœux 2..14, le gain est de
-- 1, pas de 14.)
--
-- Si un candidat précédemment admis ne l'est plus, comparer renvoie
-- Nothing, qu'on peut interpréter comme une badness infinie.
comparer :: Parcoursup -> Parcoursup -> Maybe Int
comparer p p' =  fmap sum $ sequence  (fmap comp z)
  where
    comp :: (Proposition, Proposition) -> Maybe Int
    comp ((c, p), (c', p')) | c == c' = Just $ p - p'
                            | otherwise = Nothing
    z = zip (propositions . finaliser $ p) (propositions . finaliser $ p')


-- erm = fmap sum $ sequence [Just 1, Just 2, Just 3, Nothing]


-- | Supprime les listes d'attente
finaliser :: Parcoursup -> Parcoursup
finaliser = fmap (\f -> f { fAdmis = take (capacite f) (fAdmis f) })

-- | Normalise les rangs de préférence des candidats sur l'intervalle
-- [1..x], sans interruption. Cette opération est nécessaire à rendre
-- la comparaison par `compare` indépendante du rang absolu des
-- préférences.
normaliser :: Parcoursup -> Parcoursup
normaliser p = changeFormations trans p
  where
    trans = fmap (\(cand, préf) -> (cand, mapLookup2' cand préf norm))
    norm = fmap (\x -> M.fromList $ zip x [1..]) . M.fromListWith (++) . fmap (\(a,b) -> (a, [b])) . reverse . sort $ foldMap fAdmis p

-- | Renvoie la liste triée des propositions
propositions :: Parcoursup -> [Proposition]
propositions = sort . foldMap fAdmis

-- * Utilitaires

-- | Supprime un vœu
abandonVoeu :: IdFormation -> Candidat -> Parcoursup -> Parcoursup
abandonVoeu f c = fmap av
  where
    av :: Formation -> Formation
    av f' | f == fId f' = f' {fAdmis = filter (\x -> fst x /= c) (fAdmis f')}
          | otherwise = f'

-- | Utilitaire: applique récursivement une fonction jusqu'à ce
-- qu'elle soit stable.
stabilise :: (Eq a) => (a -> a) -> a -> a
stabilise f x = let
  x' = f x
  in
    if x /= x' then stabilise f x' else x'

-- | Retourne pour chaque candidat le plus haut rang de préférence
-- d'un vœu admis.
meilleurAdmis :: Parcoursup -> M.Map Candidat Int
meilleurAdmis fs = foldr (M.unionWith min) M.empty (fmap m fs)
  where
    m f = M.fromList $ take (capacite f) (fAdmis f)

-- | Retourne pour chaque candidat le plus haut rang de préférence
-- d'un vœu.
meilleur :: Parcoursup -> M.Map Candidat Int
meilleur fs = foldr (M.unionWith min) M.empty (fmap m fs)
  where
    m f = M.fromList (fAdmis f)

-- * Interface

main :: IO ()
main = putStrLn "Parcoursup!"

-- * Les cas de test

candidats = ['A'..'J']
casSimple :: Parcoursup
casSimple = [Formation 0 3 [('A', 8)
                           , ('B', 7)
                           , ('C', 6)
                           , ('D', 4)
                           , ('E', 1)]]

casSimple2 = [Formation 0 3 [('A', 8)
                            , ('B', 7)
                            , ('C', 6)
                            , ('D', 4)
                            , ('E', 1)]
             , Formation 1 1 [('F', 8)
                            , ('G', 7)
                            , ('H', 6)
                            , ('A', 1)
                            , ('E', 2)]]

casSimple2NonNormalisé = [Formation 0 3 [('A', 80)
                                        , ('B', 70)
                                        , ('C', 60)
                                        , ('D', 40)
                                        , ('E', 10)]
                         , Formation 1 1 [('F', 80)
                                         , ('G', 70)
                                         , ('H', 60)
                                         , ('A', 10)
                                         , ('E', 20)]]

simpleDeadLock = [Formation 0 1 [('A', 2)
                            , ('B', 1)]
                 , Formation 1 1 [('B', 2)
                            , ('A', 1)]]

-- | Un cas où rien ne va. Tous les candidats sont classés dans
-- l'ordre inverse de leurs préférences.  La solution optimale est que
-- chacun est admis dans son premier vœu.
pireCas :: Parcoursup
pireCas = fmap mk [0..9]
  where
    mk i = Formation i 1 (liste i)
    liste i = zip ((drop i candidats) ++ (take i candidats)) [9,8..1]

fshow :: Parcoursup -> String
fshow f = foldMap (\x -> show (fId x) ++ " ==> " ++ show (fAdmis x) ++ "\n") f
  where
    lengths = fmap (length . fAdmis) f
    f' =  fmap fAdmis f

tentative1 = normaliser . phase1 $ pireCas
tentative2 = normaliser . phase1 . abandonVoeu 0 'A' $ pireCas
tentative3 = normaliser . phase1 . abandonVoeu 0 'B'
  . abandonVoeu 1 'B'
  . abandonVoeu 2 'B'
  . abandonVoeu 3 'B'
  . abandonVoeu 4 'B'
  . abandonVoeu 6 'B'
  . abandonVoeu 7 'B'
  . abandonVoeu 8 'B'
  . abandonVoeu 9 'B'
  $ pireCas

changeFormations :: ([Proposition] -> [Proposition]) -> Parcoursup -> Parcoursup
changeFormations f = fmap (\x -> x { fAdmis = f (fAdmis x)} )

mapLookup2 :: (Ord a, Ord b) => a -> b -> (M.Map a (M.Map b c)) -> Maybe c
mapLookup2 k1 k2 m = do
  m2 <- M.lookup k1 m
  M.lookup k2 m2

mapLookup2' :: (Ord a, Ord b) => a -> b -> (M.Map a (M.Map b c)) -> c
mapLookup2' k1 k2 =  fromJust . mapLookup2 k1 k2
