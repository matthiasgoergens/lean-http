import Lake
open Lake DSL

package probe

@[default_target]
lean_exe timerprobe where
  root := `TimerProbe

lean_exe exitprobe where
  root := `ExitProbe
