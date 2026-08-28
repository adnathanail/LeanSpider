import LSpec
import SpLean.Algebraic.AlgPhase

namespace Tests.Algebraic.AlgPhase

open LSpec SpLean.Algebraic

private def zero : _root_.AlgPhase := 0
private def pi : _root_.AlgPhase := π
private def twoPi : _root_.AlgPhase := 2
private def piOverTwo : _root_.AlgPhase := π/2
private def minusPi : _root_.AlgPhase := -1
private def minusPiOverTwo : _root_.AlgPhase := -π/2
private def threePi : _root_.AlgPhase := 3

private def formatTests : TestSeq :=
  group "format" $
    test "zero" (zero.format = "0") $
    test "pi" (pi.format = "π") $
    test "two pi" (twoPi.format = "2π") $
    test "pi over two" (piOverTwo.format = "π/2") $
    test "minus pi" (minusPi.format = "-π") $
    test "minus pi over two" (minusPiOverTwo.format = "-π/2")

/-! Display, pinned. `AlgPhase.format` above is the string a *closed* phase is
drawn with; these are the pretty-printer forms, which is what a symbolic phase
reaches the viewer as (see `SpLean/Algebraic/Render.lean`). They are what
`unexpandOfRat` in `AlgPhase/Notation.lean` exists to get right: the specific
shapes have to be matched before the general `kπ`, or `π` prints as `1π` and
`π/4` as `1 / 4π`. -/

/-- info: π : AlgPhase -/
#guard_msgs in #check (π : _root_.AlgPhase)

/-- info: π/4 : AlgPhase -/
#guard_msgs in #check (π/4 : _root_.AlgPhase)

/-- info: 3π/4 : AlgPhase -/
#guard_msgs in #check (3π/4 : _root_.AlgPhase)

/-- info: 2π : AlgPhase -/
#guard_msgs in #check (2π : _root_.AlgPhase)

/-- info: fun α => α + π/4 : AlgPhase → AlgPhase -/
#guard_msgs in #check fun (α : _root_.AlgPhase) => α + π/4

private def normalizationTests : TestSeq :=
  group "normalization" $
    test "pi ≠ 3 pi" (pi ≠ threePi) $
    test "pi equiv 3 pi" (pi.equiv threePi)

def tests : TestSeq :=
  group "AlgPhase" $
    formatTests ++
    normalizationTests

#lspec tests

end Tests.Algebraic.AlgPhase
