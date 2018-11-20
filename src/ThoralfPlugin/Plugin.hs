
module ThoralfPlugin.Plugin ( plugin ) where


import GhcPlugins ( Plugin (..), defaultPlugin )
import TcRnTypes  ( TcPlugin (..) )

import ThoralfPlugin.Encode ( thoralfTheories )
import ThoralfPlugin.ThoralfPlugin ( thoralfPlugin )


plugin :: Plugin
plugin = defaultPlugin {tcPlugin = const (Just currentPlugin)}

-- The Boolean is for debugging
currentPlugin :: TcPlugin
currentPlugin = thoralfPlugin True thoralfTheories


