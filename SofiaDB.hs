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
    name      String
    schema    String
    params    Int
    desc      String
    AxiomName name
    deriving Show
|]

runSqlite' :: (MonadUnliftIO m) => Text -> ReaderT SqlBackend (NoLoggingT (ResourceT m)) a -> m a
runSqlite' = runSqlite

main :: IO ()
main = runSqlite' "theory.db" $ do
    {-runMigration migrateAll
    t <- insert $ AxiomBuilder "Restricted Comprehension"
                          ("{\"[ [[]] :[ [[]] : [[]] [ [[]] :[ [ [[]] in [[]] ] =[[]:[ [[]] in [[]] ] [[]] ]]]]]\", 0, " ++
                           "   [ 2,      5,     4,     3,        3,      4,            3,      5,     1        ]}")
                          5
                          ""
    insert $ AxiomBuilder "Induction"
        ("{\"[ [[]] [             [[]] [ [[]] nat] [[]] : [[]] ]:[                        [[]] [ [[]] nat]: [[]] ]]\", 0, " ++
     "   [ {1, 3, \"[0[]]\"}, 3,     3,        1,     {1, 3, {\"[1+[[]]]\", 0, [3]}}, 3,     3,         1             ]}")
        3
        "" -- -}
    axiom_builders <- selectList [AxiomBuilderParams >. 0] []
    liftIO $ print $ Prelude.map axiomBuilderSchema $ Prelude.map entityVal axiom_builders
