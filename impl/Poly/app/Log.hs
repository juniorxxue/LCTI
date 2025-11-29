{-# LANGUAGE RankNTypes #-}

module Log where

import Control.Monad.Writer
import qualified Data.Text as T
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle, renderStrict)
import qualified Prettyprinter.Render.Terminal as Ansi
import Syntax

type LogDoc = Doc AnsiStyle

renderLogDoc :: LogDoc -> String
renderLogDoc = T.unpack . renderStrict . layoutPretty defaultLayoutOptions

prettyShowDoc :: Show a => a -> LogDoc
prettyShowDoc = pretty . show

withStyle :: AnsiStyle -> LogDoc -> LogDoc
withStyle style = annotate style

grey, red, bold, blue, yellow :: LogDoc -> LogDoc
grey = withStyle (Ansi.color Ansi.Black)
red = withStyle (Ansi.color Ansi.Red)
blue = withStyle (Ansi.color Ansi.Blue)
yellow = withStyle (Ansi.color Ansi.Yellow)
bold = withStyle Ansi.bold

logLine :: [LogDoc] -> String
logLine = renderLogDoc . hsep

symbol :: String -> LogDoc
symbol = pretty

semiDoc :: LogDoc
semiDoc = grey (symbol ";")

envDoc :: Env -> LogDoc
envDoc = prettyShowDoc

blueEnv :: Env -> LogDoc
blueEnv = blue . envDoc

redEnv :: Env -> LogDoc
redEnv = red . envDoc

tyDoc :: Ty -> LogDoc
tyDoc = prettyShowDoc

ctxDoc :: Context -> LogDoc
ctxDoc = prettyShowDoc

tmDoc :: Tm -> LogDoc
tmDoc = prettyShowDoc

logSub :: Env -> Ty -> Context -> String
logSub senv ty ctx =
  logLine [envDoc senv, symbol "⊢", tyDoc ty, pretty "<:", ctxDoc ctx, symbol "⊣"]

logInferUncurry :: (Env, Env) -> Ty -> Tm -> Ty -> Env -> String
logInferUncurry (_, senv) tyA e tyA' envout =
  logLine
    [ semiDoc
    , blueEnv senv
    , symbol "⊢"
    , tyDoc tyA
    , pretty "⇉"
    , tmDoc e
    , pretty "⇉"
    , bold (tyDoc tyA')
    , symbol "⊣"
    , redEnv envout
    ]

logSubFull :: (Env, Env) -> Ty -> Context -> Env -> Ty -> String
logSubFull (_, senv) ty ctx envout ty' =
  logLine
    [ semiDoc
    , blueEnv senv
    , symbol "⊢"
    , tyDoc ty
    , pretty "<:"
    , ctxDoc ctx
    , symbol "⊣"
    , redEnv envout
    , pretty "⇝"
    , bold (tyDoc ty')
    ]

logSSubFull :: (Env, Env) -> Ty -> Polar -> Ty -> Env -> String
logSSubFull (_, senv) ty1 p ty2 envout =
  logLine
    [ semiDoc
    , blueEnv senv
    , symbol "⊢"
    , tyDoc ty1
    , pretty (show p)
    , tyDoc ty2
    , symbol "⊣"
    , redEnv envout
    ]

logInfers :: Env -> Context -> String
logInfers env ctx = logLine [envDoc env, symbol "⊢", ctxDoc ctx, pretty "⇒"]

logInfersFull :: Env -> Context -> Ty -> String
logInfersFull _ ctx ty =
  logLine [grey (symbol "⊢"), ctxDoc ctx, pretty "⇒", bold (tyDoc ty)]

logInfer :: Env -> Context -> Tm -> String
logInfer env ctx tm = logLine [envDoc env, symbol "⊢", ctxDoc ctx, pretty "⇒", tmDoc tm, pretty "⇒"]

logInferFull :: Env -> Context -> Tm -> Ty -> String
logInferFull _ ctx tm ty =
  logLine [grey (symbol "⊢"), ctxDoc ctx, pretty "⇒", tmDoc tm, pretty "⇒", bold (tyDoc ty)]

indentAll :: [String] -> [String]
indentAll = map ("  " ++)

peek :: forall w m a. (MonadWriter w m) => m a -> m (a, w)
peek = censor (const mempty) . listen

formatError :: String -> [(String, String)] -> String
formatError msg context =
  renderLogDoc $
    header <> contextBlock
  where
    header = bold (red (pretty "ERROR:")) <+> bold (pretty msg)
    contextBlock
      | null context = mempty
      | otherwise = hardline <> vsep (map renderPair context)
    renderPair (label, value) =
      indent 2 (yellow (pretty label) <> pretty ":" <+> pretty value)
