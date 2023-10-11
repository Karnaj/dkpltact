- use "definition"
- include('command.ax')




Definition nCol (A: Point) (B: Point) (C: Point)  := (A != B) & (A != C) & (B != C) & ~BetS A B C & ~BetS A C B & ~BetS B A C.


ttf(bets, ...)
ttf(ncol, ...)
ttf(ncol_eq, def, ...)


nCol(A, b, C) => 
----
nCOl(A,b, C) => f(A)

