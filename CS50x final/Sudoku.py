'''
Goal of Sudoku: Fill the grid so that every row, column, and box contains the digits from 1 to 9 once each.
'''

class SudokuError(Exception):
    pass


class RegionQueue:
    def __init__(self):
        self.high = []
        self.low = []
    

    def enqueue(self, region, priority=2):
        if region in self.high:
            return
        if priority == 2:
            self.high.append(region)
            if region in self.low:
                self.low.remove(region)
            return
        if region not in self.low:
            self.low.append(region)
            

    def dequeue(self, priority):
        if priority == 2:
            return self.high.pop(0)
        return self.low.pop(0)
    

    def isempty(self):
        return len(self.high) == len(self.low) == 0


    def print(self):
        print("Queue:", end="")
        for item in self.queue:
            print(f" {item} ", end="")
        print()


class Cell:
    def __init__(self, value=0, canSet=None):
        if not value or value == "0":
            self.value = 0
            if canSet:
                self.cans = canSet
            else:
                self.cans = set(range(1,10))
        else:
            self.value = int(value)
            self.cans = {self.value}
        self.regions = set()


    def print(self):
        if self.value == 0:
            print(self.cans)
        else:
            print(self.value)
    

    def copy(self):
        newCan = {can for can in self.cans}
        newCell = Cell(self.value, newCan)
        return newCell


class Region:
    def __init__(self):
        self.cells = [] # List of cells in the region. Not a set since when we copy the region we need to match corresponding cells
        self.knowns = set()
        self.sudoku = None
    

    def addCell(self, cell):
        self.cells.append(cell)
        if cell.value:
            self.knowns.add(cell.value)
        cell.regions.add(self)
    

    def updateKnowns(self):
        for cell in self.cells:
            if cell.value:
                self.knowns.add(cell.value)
    

    def enqueue(self, cell):
        '''
        Enqueue the other regions associated with cell with high priority.
        Does nothing if this region is a copy.
        '''
        for region in cell.regions - {self}:
            self.sudoku.queue.enqueue(region)


    def cleanCell(self, cell):
        '''
        Elim candidates known in region.
        Note that if a cell has value 0 but one candidate then this candidate becomes the value,
        gets added to self.knowns, and the cell's other two regions get enqueued with high priority.
        '''
        length1 = len(cell.cans)
        cell.cans -= self.knowns
        length2 = len(cell.cans)
        match length2:
            case 1:  # Important to do this first in case length1 = 1
                value, = cell.cans
                cell.value = value
                for region in cell.regions:
                    if value in region.knowns:
                        return -1
                    region.knowns.add(value)
                self.enqueue(cell)
                return 2
            case x if x == length1:
                return 0
            case x if x > 1:
                return 1
            case _: # cell.cans is empty
                return -1


    def clean1(self):
        elimCan = 0
        newKnown = 0
        repeat = True
        while repeat:
            repeat = False
            for cell in self.cells:
                if not cell.value:
                    match self.cleanCell(cell):
                        case 0:
                            pass
                        case 1:
                            repeat = True
                            elimCan = 1
                        case 2:
                            repeat = True
                            elimCan = 1
                            newKnown = 1
                        case -1:
                            return -1
        if len(self.knowns) == 9:
            return 3
        if elimCan:
            self.sudoku.queue.low.append(self)
        return elimCan + newKnown
    

    def hiddenSingles(self):
        ucount = [0] * 9
        output = 0
        for cell in self.cells:
            if not cell.value:
                for can in cell.cans:
                    ucount[can - 1] += 1
        
        for i in range(1, 10):
            if ucount[i - 1] == 1:
                for cell in self.cells:
                    if i in cell.cans:  # Find unique cell with i as a candidate
                        break
                cell.cans = {i}  # We run clean1() afterwards so no need to do anything else here
                output = 2
        return output
    

    def copy(self):
        newRegion = Region()
        for cell in self.cells:
            newRegion.addCell(cell.copy())
        return newRegion


    def print(self):
        print("values: ", end="")
        for cell in self.cells:
            print(cell.value, end="  ")
        print()
        for cell in self.cells:
            if not cell.value:
                print(cell.cans)


class Sudoku:

    def __init__(self, grid):
        self.givens = grid
        self.grid = []
        for row in range(9):
            self.grid.append([])
            for col in range(9):
                self.grid[row].append(Cell(grid[row][col]))

        self.regions = []
        for row in range(9): # Rows
            self.regions.append(Region())
            for col in range(9):
                self.regions[row].addCell(self.grid[row][col])
        for col in range(9): # Columns
            self.regions.append(Region())
            for row in range(9):
                self.regions[col + 9].addCell(self.grid[row][col])
        for box in range(9): # Boxes
            self.regions.append(Region())
            for row in range(box - box % 3, box - box % 3 + 3):
                for col in range(3 * (box % 3), 3 * (box % 3) + 3):
                    self.regions[box + 18].addCell(self.grid[row][col])

        self.queue = RegionQueue()
        for region in self.regions:
            region.sudoku = self
            if region.knowns:
                self.queue.enqueue(region)
        
        self.depth = -1


    def getCell(self, index): # Returns a cell in reading order
        return self.grid[index // 9][index % 9]
    

    def solved(self):
        for i in range(9):  # Suffices to just check the rows
            if len(self.regions[i].knowns) != 9:
                return 0
        return 3


    def solve0(self):
        while not self.queue.isempty():
            if self.queue.high:
                region = self.queue.dequeue(2)
                if region.clean1() == -1:
                    return -1
            else:
                region = self.queue.dequeue(1)
            while region.hiddenSingles():
                match region.clean1():
                    case -1:
                        return -1
                    case 0:
                        break
                    case 3:
                        break
        return self.solved()
    

    def solve1(self):  # Slow solve. Checks for multiple solutions.
        match self.solve0():
            case 0:
                pass
            case 3:
                self.depth = 0
                return 3
            case -1:
                raise SudokuError("Puzzle has no solution")
    
        global SOLUTION  # Store the solution in this 9x9 grid
        SOLUTION = [[None] * 9 for _ in range(9)]
        
        i = 0  # Find a cell with an unknown value
        while self.getCell(i).value:
            i = i + 1
        cell = self.getCell(i)

        solution_found = False
        
        for can in cell.cans:
            newSudoku = self.copy()
            newSudoku.getCell(i).cans = {can}
            if newSudoku.solve1_inner(i, 1) == 3:
                solution_found = True
        
        if not solution_found:
            raise SudokuError("Puzzle has no solution")
        
        for i in range(81):
            cell = self.getCell(i)
            value = SOLUTION[i // 9][i % 9]
            cell.value = value
            cell.cans = {value}
            for region in cell.regions:
                region.knowns.add(value)
        
        self.depth = DEPTH


    def solve1_inner(self, index, depth):
        '''
        Try solve0().
        If unsuccessful then pick an unknown cell and iterate through candidates, copying the
        sudoku and running solve1_inner with each candidate.
        If successful and we've already found a solution (if SOLVED) then raise an error: puzzle
        has multiple solutions.
        If successful and this is the first solution we've found then populate the SOLUTION grid
        '''
        for region in self.getCell(index).regions:
            self.queue.enqueue(region)
        match self.solve0():
            case -1:
                return -1
            case 3:
                global DEPTH
                DEPTH = depth
                global SOLUTION
                if SOLUTION[0][0]:  # Solution already solved
                    raise SudokuError("Puzzle has more than one solution")
                for row in range(9):
                    for col in range(9):
                        SOLUTION[row][col] = self.getCell(9 * row + col).value
                return 3
                            
        i = 0  # Find an unknown cell
        while self.getCell(i).value:
            i = i + 1
        cell = self.getCell(i)

        output = -1

        for can in cell.cans:
            newSudoku = self.copy()
            newSudoku.getCell(i).cans = {can}
            if newSudoku.solve1_inner(i, depth + 1) == 3:
                output = 3
        
        return output
    

    def solve2(self):  # Fast solve. Doesn't check for multiple solutions.
        match self.solve0():
            case 0:
                pass
            case 3:
                self.depth = 0
                return 3
            case -1:
                raise SudokuError("Puzzle has no solution")
    
        global SOLUTION  # Store the solution in this 9x9 grid
        SOLUTION = [[0] * 9 for _ in range(9)]

        i = 0
        while self.getCell(i).value:
            i = i + 1
        cell = self.getCell(i)
        
        for can in cell.cans:
            newSudoku = self.copy()
            newSudoku.getCell(i).cans = {can}
            if newSudoku.solve2_inner(i, 1) == 3:
                for i in range(81):
                    cell = self.getCell(i)
                    value = SOLUTION[i // 9][i % 9]
                    cell.value = value
                    cell.cans = {value}
                    for region in cell.regions:
                        region.knowns.add(value)
                self.depth = DEPTH
                return 3
        
        raise SudokuError("Puzzle has no solution")


    def solve2_inner(self, index, depth):
        '''
        Try solve0().
        If unsuccessful then pick an unknown cell and iterate through candidates, copying the
        sudoku and running solve1_inner with each candidate.
        If successful and we've already found a solution (if SOLVED) then raise an error: puzzle
        has multiple solutions.
        If successful and this is the first solution we've found then populate the SOLUTION grid
        '''
        for region in self.getCell(index).regions:
            self.queue.enqueue(region)

        match self.solve0():
            case -1:
                return -1
            case 3:
                global SOLUTION
                for row in range(9):
                    for col in range(9):
                        SOLUTION[row][col] = self.getCell(9 * row + col).value
                global DEPTH
                DEPTH = depth
                return 3
                            
        i = 0
        while self.getCell(i).value:
            i = i + 1
        cell = self.getCell(i)

        for can in cell.cans:
            newSudoku = self.copy()
            newSudoku.getCell(i).cans = {can}
            if newSudoku.solve2_inner(i, depth + 1) == 3:
                return 3
        
        return -1


    def copy(self):
        grid = []
        for row in range(9):
            newRow = []
            for col in range(9):
                newRow.append(self.grid[row][col].value)
            grid.append(newRow)
        newSudoku = Sudoku(grid)
        for i in range(81):
            newCell = newSudoku.getCell(i)
            oldCell = self.getCell(i)
            newCell.cans = {can for can in oldCell.cans}
        return newSudoku
    

    def restore(self):
        self.__init__(self.givens)
    

    def print(self):
        hborder = "+-------+-------+-------+"
        for row in range(9):
            if row % 3 == 0:
                print(hborder)
            for col in range(9):
                if col % 3 == 0:
                    print("|", end=" ")
                value = self.grid[row][col].value
                if value > 0:
                    print(value, end=" ")
                else:
                    print("  ", end="")
            print("|")
        print(hborder)
    

def transpose(grid):
    output = [[None] * 9 for _ in range(9)]
    for row in range(9):
        for col in range(9):
            output[row][col] = grid[col][row]
    return output


def rotate(grid):
    output = [[None] * 9 for _ in range(9)]
    for row in range(9):
        for col in range (9):
            output[row][col] = grid[8 - col][row]
    return output


def difficulty(grid):
    count = 0

    for _ in range(4):
        my_sudoku = Sudoku(grid)
        my_sudoku.solve2()
        count += my_sudoku.depth
        grid = rotate(grid)

    grid = transpose(grid)

    for _ in range(4):
        my_sudoku = Sudoku(grid)
        my_sudoku.solve2()
        count += my_sudoku.depth
        grid = rotate(grid)

    return count/8