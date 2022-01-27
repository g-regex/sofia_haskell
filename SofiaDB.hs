{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

import           Control.Monad.IO.Class  (liftIO)
import           Database.Persist
import           Database.Persist.Sqlite
import           Database.Persist.TH
import           Control.Monad.IO.Unlift
import           Data.Text
import           Control.Monad.Reader
import           Control.Monad.Logger
import           Conduit

import           Sofia
import           SofiaAxiomParser

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
AxiomBuilder
    rubric    String
    name      String
    schema    String
    params    Int
    desc      String
    hist      String
    Axiom     rubric name
    deriving Show
|]

runSqlite' :: (MonadUnliftIO m) => Text -> ReaderT SqlBackend (NoLoggingT (ResourceT m)) a -> m a
runSqlite' = runSqlite

main :: IO ()
main = runSqlite' "theory.db" $ do
    {-runMigration migrateAll
    insert $ AxiomBuilder "" "Restricted Comprehension"
        "{`[ [[]] :[ [[]] : [[]] [ [[]] :[ [ [[]] in [[]] ] =[[]:[ [[]] in [[]] ] [[]] ]]]]]`, 0, [2, 5, 4, 3, 3, 4, 3, 5, 1]}"
        5
        "When invoked with the parameters [\"[alpha[x]]\",\"[C][D]\",\"[x]\",\"[A]\",\"[B]\"], the axiom [[C][D]:[[B]:[A][[x]:[[[x] in [A]]=[[]:[[x] in [B]][alpha[x]]]]]]] will be recalled."
        ""
    insert $ AxiomBuilder "Arithmetic" "Induction"
        "{`[ [[]] [ [[]] [ [[]] nat] [[]] : [[]] ]:[ [[]] [ [[]] nat]: [[]] ]]`, 0, [ {1, 3, `[0[]]`}, 3, 3, 1, {1, 3, {`[1+[[]]]`, 0, [3]}}, 3, 3, 1]}"
        3
        "When invoked with the parameters [\"[blabla[n][m][k]]\",\"[m][k]\",\"[n]\"], the axiom stating that for all [m][k], the statement [blabla[n][m][k]] can be proven by induction on [n], will be recalled."
        ""
    insert $ AxiomBuilder "Arithmetic" "Zero"
        "{`[0[]][[0[]]nat][[n][[n]nat][[0[]]=[1+[n]]]:[![]]]`, 0, []}"
        0
        "Stating properties of the number zero."
        ""
    insert $ AxiomBuilder "Arithmetic" "Successor"
        "{`[[n][[n]nat]:[1+[n]][[1+[n]]nat][[m][[m]nat][[1+[n]]=[1+[m]]]:[[n]=[m]]]]`, 0, []}"
        0
        "Stating properties of the successor function."
        ""
    insert $ AxiomBuilder "Boolean" "False Universality"
        "{`[ [[]] [![]]: [[]] ]`, 0, [2, 1]}"
        2
        "When invoked with the parameters [\"[blabla[X][Y]]\",\"[X][Y]\"], the axiom [[X][Y][![]]:[blabla[X][Y]]] will be recalled."
        ""
    insert $ AxiomBuilder "Boolean" "Double Negation"
        "{`[ [[]] [[ [[]] :[![]]]:[![]]]: [[]] ]`, 0, [2, 1, 1]}"
        2
        "When invoked with the parameters [\"[blabla[X][Y]]\",\"[X][Y]\"], the axiom [[X][Y][[[blabla[X][Y]]:[![]]]:[![]]]:[blabla[X][Y]]] will be recalled."
        ""
    -- -}
    axiom_builders <- selectList [AxiomBuilderParams >. 0] []
    liftIO $ print $ Prelude.map axiomBuilderSchema $ Prelude.map entityVal axiom_builders
