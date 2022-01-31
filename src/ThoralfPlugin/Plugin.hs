{-# LANGUAGE CPP #-}

module ThoralfPlugin.Plugin ( plugin ) where


#if MIN_VERSION_ghc(9, 2, 0)
import GHC.Plugins ( Plugin (..), defaultPlugin )
import GHC.Tc.Types ( TcPlugin(..) )
#else
import GhcPlugins ( Plugin (..), defaultPlugin )
import TcRnTypes  ( TcPlugin (..) )
#endif

import ThoralfPlugin.Encode ( thoralfTheories )
import ThoralfPlugin.ThoralfPlugin ( thoralfPlugin )


plugin :: Plugin
plugin = defaultPlugin {tcPlugin = const (Just currentPlugin)}

-- The Boolean is for debugging
currentPlugin :: TcPlugin
currentPlugin = thoralfPlugin False thoralfTheories


