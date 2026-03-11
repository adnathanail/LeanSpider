/-- Extract the value from an Except, panicking on error -/
def Except.get! [Inhabited α] : Except ε α → α
  | .ok a => a
  | .error _ => panic! "Except.get! called on .error"

/-- Check if an Except is an error -/
def Except.isError : Except ε α → Bool
  | .ok _ => false
  | .error _ => true

/-- Convert an Option to Except, using the given error message for `none` -/
def Option.toExcept (msg : String) : Option α → Except String α
  | some a => .ok a
  | none => .error msg

/-- Insert an element into a sorted list (structural recursion, kernel-reducible) -/
def List.orderedInsert [Ord α] (a : α) : List α → List α
  | [] => [a]
  | b :: l => if (compare a b).isLE then a :: b :: l else b :: List.orderedInsert a l

/-- Insertion sort using structural recursion (kernel-reducible, unlike mergeSort) -/
def List.insertionSort [Ord α] : List α → List α
  | [] => []
  | a :: l => (List.insertionSort l).orderedInsert a
