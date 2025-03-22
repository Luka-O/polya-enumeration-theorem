import PolyaEnumerationTheorem.Concrete

-- The number of distinct colorings of a necklace with `100` beads and `100` colors. The necklace can be rotated, but not reflected.
#eval Necklaces.computeNumDistinctColoringsOfNecklace 100 100

-- The number of distinct colorings of a bracelet with `100` beads and `100` colors. The bracelet can be rotated and reflected.
#eval Bracelets.computeNumDistinctColoringsOfBracelet 100 100

-- The number of distinct colorings of a cube's faces using `100` colors.
#eval Cube.computeNumDistinctColoringsOfCube 100
