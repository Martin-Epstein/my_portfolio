from Sudoku import *

nyt_easy = [
    [0, 1, 0,  0, 2, 0,  8, 3, 0],
    [0, 2, 4,  0, 5, 9,  7, 0, 0],
    [0, 5, 6,  7, 1, 0,  0, 0, 0],

    [5, 8, 3,  2, 0, 0,  0, 6, 0],
    [0, 0, 7,  6, 8, 0,  3, 0, 4],
    [0, 0, 0,  5, 7, 0,  0, 8, 2],

    [0, 0, 0,  9, 0, 2,  6, 0, 8],
    [4, 0, 8,  0, 0, 5,  0, 0, 0],
    [9, 6, 0,  0, 0, 7,  0, 0, 1]
]

nyt_medium = [
    [0, 0, 0,  0, 4, 7,  0, 0, 0],
    [1, 7, 0,  0, 0, 5,  0, 0, 0],
    [0, 0, 0,  0, 0, 9,  0, 0, 5],

    [8, 0, 0,  3, 7, 0,  2, 0, 0],
    [0, 0, 3,  0, 5, 8,  0, 0, 4],
    [5, 0, 0,  6, 0, 0,  0, 0, 0],

    [2, 0, 0,  0, 0, 0,  3, 0, 0],
    [0, 5, 0,  0, 0, 0,  0, 0, 9],
    [4, 0, 0,  0, 2, 0,  0, 0, 0]
]

nyt_hard = [
    [0, 2, 4,  0, 0, 3,  0, 9, 0],
    [0, 0, 0,  0, 0, 0,  5, 3, 7],
    [0, 0, 0,  0, 6, 0,  0, 0, 1],

    [0, 3, 0,  0, 0, 0,  0, 0, 5],
    [0, 8, 0,  0, 0, 0,  0, 0, 0],
    [0, 0, 1,  0, 9, 0,  0, 6, 0],

    [5, 0, 0,  0, 2, 0,  0, 0, 0],
    [8, 7, 9,  0, 0, 5,  0, 0, 3],
    [0, 0, 3,  0, 0, 0,  0, 0, 0]
]

extremely_hard = [
    [0, 0, 0,  1, 0, 2,  0, 0, 0],
    [0, 6, 0,  0, 0, 0,  0, 7, 0],
    [0, 0, 8,  0, 0, 0,  9, 0, 0],

    [4, 0, 0,  0, 0, 0,  0, 0, 3],
    [0, 5, 0,  0, 0, 7,  0, 0, 0],
    [2, 0, 0,  0, 8, 0,  0, 0, 1],

    [0, 0, 9,  0, 0, 0,  8, 0, 5],
    [0, 7, 0,  0, 0, 0,  0, 6, 0],
    [0, 0, 0,  3, 0, 4,  0, 0, 0]
]

nonunique = [[0] * 9 for _ in range(9)]

nonunique[0][0] = 1
nonunique[0][8] = 2
nonunique[8][0] = 3
nonunique[8][8] = 4

impossible = [
    [0, 1, 0,  0, 0, 7,  2, 0, 0],
    [0, 0, 0,  0, 3, 0,  9, 0, 0],
    [0, 0, 8,  0, 1, 0,  0, 3, 7],

    [0, 2, 0,  0, 0, 0,  0, 9, 1],
    [3, 4, 0,  8, 7, 0,  0, 0, 0],
    [0, 6, 0,  0, 0, 0,  4, 0, 0],

    [5, 0, 2,  4, 0, 0,  0, 0, 3],
    [4, 0, 3,  0, 5, 0,  0, 0, 0],
    [0, 1, 0,  0, 0, 0,  0, 0, 0]
]

input("Initializing Sudoku (New York Times easy difficulty)...")
my_sudoku = Sudoku(nyt_easy)
my_sudoku.print()

input("Solving ( solve0() )...")
my_sudoku.solve0()
my_sudoku.print()

input("Initializing Sudoku (New York Times hard difficulty)...")
my_sudoku = Sudoku(nyt_hard)
my_sudoku.print()

input("Attempting to Sudoku ( solve0() )...")
my_sudoku.solve0()
my_sudoku.print()

input("Solving Sudoku ( solve1() )...")
my_sudoku.solve1()
my_sudoku.print()

input("What if the puzzle has no solution?")
input("Initializing Sudoku (impossible)...")
my_sudoku = Sudoku(impossible)
my_sudoku.print()

input("Solving Sudoku ( solve1() )")
try:
    my_sudoku.solve1()
except SudokuError:
    print("SudokuError: Puzzle has no solution")

input("What if the puzzle has more than one solution?")
input("Initializing Sudoku (nonunique)...")
my_sudoku = Sudoku(nonunique)
my_sudoku.print()

input("Solving Sudoku ( solve1() )")
try:
    my_sudoku.solve1()
except SudokuError:
    print("SudokuError: Puzzle has more than one solution")

input("What if I don't need to check if the solution is unique?")
input("Reinitializing nonunique Sudoku...")
my_sudoku.restore()

input("Solving Sudoku ( solve2() )")
my_sudoku.solve2()
my_sudoku.print()

input("How hard is my puzzle?")

input("Printing (New York Times easy)...")
Sudoku(nyt_easy).print()

input("Calculating difficulty (New York Times easy)...")
print(difficulty(nyt_easy))

input("Printing (New York Times medium)...")
Sudoku(nyt_medium).print()

input("Calculating difficulty (New York Times medium)...")
print(difficulty(nyt_medium))

input("Printing (New York Times hard)...")
Sudoku(nyt_hard).print()

input("Calculating difficulty (New York Times hard)...")
print(difficulty(nyt_hard))

input("Printing (Cracking The Cryptic extremely hard)...")
Sudoku(extremely_hard).print()

input("Calculating difficulty (Cracking The Cryptic extremely hard)...")
print(difficulty(extremely_hard))