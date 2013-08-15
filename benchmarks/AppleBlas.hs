
module AppleBlas(blasMMult) where



import Foreign hiding (unsafePerformIO)
import Foreign.C.Types
import Unsafe.Coerce
import Prelude hiding (replicate)
--import Data.Storable
import System.IO.Unsafe
import Data.Vector.Storable.Mutable  
import GHC.Ptr (castPtr)

import Numerics.Simple.Util

foreign import ccall unsafe "testAppleBlas.c simple_dgemm"
    dgemm :: Ptr CDouble -> Ptr CDouble -> Ptr CDouble -> CInt -> IO ()

saphWrapper :: (Ptr CDouble -> Ptr CDouble -> Ptr CDouble -> CInt -> IO ())-> ( Ptr Double -> Ptr Double -> Ptr Double -> Int -> IO ())
saphWrapper f = (\c a b  n -> f (castPtr c ) (castPtr a) (castPtr c )  (CInt  $ fromIntegral n ))
-- this is always safe/ok because CDouble is a newtyped Double, and CInt is a newtyped Int 

dgemm_wrapped :: Ptr Double -> Ptr Double -> Ptr Double -> Int -> IO ()
dgemm_wrapped = saphWrapper dgemm



blasMMult :: IOVector Double -> IOVector Double -> IOVector Double -> Int -> IO ()
blasMMult aVect bVect  cVect n =
    unsafeWith aVect $! \aPtr ->
               unsafeWith bVect $!  \bPtr -> 
                 unsafeWith cVect  $! \cPtr -> 
                    dgemm_wrapped aPtr bPtr cPtr n 