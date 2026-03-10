/-- Insert an element into a sorted list (structural recursion, kernel-reducible) -/
def List.orderedInsert [Ord α] (a : α) : List α → List α
  | [] => [a]
  | b :: l => if (compare a b).isLE then a :: b :: l else b :: List.orderedInsert a l

/-- Insertion sort using structural recursion (kernel-reducible, unlike mergeSort) -/
def List.insertionSort [Ord α] : List α → List α
  | [] => []
  | a :: l => (List.insertionSort l).orderedInsert a
