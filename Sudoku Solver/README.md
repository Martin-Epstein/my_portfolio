# Sudoku Solver
#### Video Demo:  https://youtu.be/wBBXi8pBXXo
#### Description:
Using this Python module you can
<ul>
<li>solve any sudoku puzzle</li>
<li>confirm that the solution is unique</li>
<li>rate the puzzle's difficulty</li>
</ul>
To begin, create a 9x9 grid of integers representing a sudoku puzzle. Use the digit 0 to represent a blank space. For example, here is the New York Times 'hard' puzzle from September 3, 2024.

```
nyt_hard = [
  [0, 0, 0,  0, 0, 0,  2, 0, 0],
  [0, 0, 0,  0, 3, 0,  9, 0, 0],
  [0, 0, 8,  0, 1, 0,  0, 3, 7],

  [0, 2, 0,  0, 0, 0,  0, 9, 1],
  [3, 4, 0,  8, 7, 0,  0, 0, 0],
  [0, 6, 0,  0, 0, 0,  4, 0, 0],

  [5, 0, 2,  4, 0, 0,  0, 0, 3],
  [4, 0, 3,  0, 5, 0,  0, 0, 0],
  [0, 1, 0,  0, 0, 0,  0, 0, 0]
]
```

<p>
Now you can create a Sudoku object:
</p>

```
from Sudoku import *

my_sudoku = Sudoku(nyt_hard)
```

The __print()__ method prints the puzzle to the terminal.

```
my_sudoku.print()

Terminal:
+-------+-------+-------+
|       |       | 2     |
|       |   3   | 9     |
|     8 |   1   |   3 7 |
+-------+-------+-------+
|   2   |       |   9 1 |
| 3 4   | 8 7   |       |
|   6   |       | 4     |
+-------+-------+-------+
| 5   2 | 4     |     3 |
| 4   3 |   5   |       |
|   1   |       |       |
+-------+-------+-------+
```

To "solve" a sudoku puzzle is to replace every blank with a positive digit in such a way that every row, column, and box contains the digits from 1 to 9 once each. The Sudoku class includes 3 solving methods: __solve0()__, __solve1()__, and __solve2()__.

<br>
<h3> solve0()</h3>

__solve0()__ is a "shallow" solver. If an unfilled position shares a region (i.e. a row, column, or box) with eight different (positive) digits then solve0() places the remaining digit in that position. Also, if a digit has been ruled out of eight different positions in a region then solve0() places that digit in the remaining position. __solve0()__ uses a queueing system to determine which region to examine at any given time.

__solve0()__ is not powerful enough to solve every sudoku puzzle. Using the above example:

```
my_sudoku.solve0()
my_sudoku.print()

Terminal:
+-------+-------+-------+
|   3   |       | 2     |
|       |   3   | 9     |
|     8 |   1 4 |   3 7 |
+-------+-------+-------+
| 8 2 7 |   4   | 3 9 1 |
| 3 4   | 8 7   |       |
|   6   |       | 4 7 8 |
+-------+-------+-------+
| 5   2 | 4     |     3 |
| 4   3 |   5   |       |
|   1   |       |       |
+-------+-------+-------+
```

At this point, a human solver might notice that both possible positions for the digit 5 in row 4 are in box 5, and therefore we can place 5 in row 6. But solve0() cannot see that far ahead, so currently 5 is still considered a candidate in several positions in row 6.
<br>
<h3>solve1()</h3>

__solve1()__ will fully solve any valid sudoku puzzle.
```
my_sudoku.solve1()
my_sudoku.print()

Terminal:
+-------+-------+-------+
| 7 3 1 | 5 6 9 | 2 8 4 |
| 2 5 4 | 7 3 8 | 9 1 6 |
| 6 9 8 | 2 1 4 | 5 3 7 |
+-------+-------+-------+
| 8 2 7 | 6 4 5 | 3 9 1 |
| 3 4 9 | 8 7 1 | 6 5 2 |
| 1 6 5 | 9 2 3 | 4 7 8 |
+-------+-------+-------+
| 5 8 2 | 4 9 7 | 1 6 3 |
| 4 7 3 | 1 5 6 | 8 2 9 |
| 9 1 6 | 3 8 2 | 7 4 5 |
+-------+-------+-------+

```

Furthermore, if there is more than one solution then solve1() will raise an error. __solve1()__ works by running __solve0()__, and if the puzzle is not complete then __solve1()__ chooses an unfilled position and starts guessing values for that position. For each guess the sudoku is copied, the guess is placed in that position in the copy, and __solve0()__ is run on the copy. This is repeated as many times as necessary until either the puzzle is solved or a contradiction is reached i.e. a position is unfillable.

Note that if solve1() guesses a value that leads to a solution it will keep guessing values to make sure there isn't a second solution. Once a solution is found and is confirmed to be unique, the original sudoku object is updated accordingly.
<br>
<h3>solve2()</h3>

__solve2()__ is similar to __solve1()__ except it does not check if the solution is unique. As a result, __solve2()__ runs maybe 30% faster than __solve1()__ on average. But the difference is only a few milliseconds.

<br>
<h3>Other methods, functions, and attributes</h3>

__Sudoku.depth__: After running __solve1()__ or __solve2()__ the __depth__ attribute will show the recursion depth at which the solution was found, or in other words how many guesses were required.

__Sudoku.givens__: This attribute stores the original 9x9 grid of integers.

__Sudoku.restore()__: This method restores the puzzle to its original state using __self.givens__.

__rotate(grid)__: This function takes a 9x9 grid and returns a copy that is rotated 90 degrees clockwise.

__transpose(grid)__: This function takes a 9x9 grid and returns a copy that is reflected along the top-left to bottom-right diagonal. In other words, it swaps the rows and columns.

__difficulty(grid)__: This function takes a 9x9 grid and returns a float which is meant to be a difficulty rating for the puzzle. First, the grid is used to create a sudoku object. Then the sudoku is solved using __solve2()__ and the depth is recorded. Then we do the same for the 7 other rotations and reflections of the grid, and we return the average of the 8 depths. This is to reduce bias, since __solve2()__ always starts guessing and checking in the top left of the grid.