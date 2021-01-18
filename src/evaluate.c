/*
  Ethereal is a UCI chess playing engine authored by Andrew Grant.
  <https://github.com/AndyGrant/Ethereal>     <andrew@grantnet.us>
  Ethereal is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  Ethereal is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/


// Modifications done
// material value reduction to buff activity
// weak squares, mobility, attacked weak squares
// connected rooks, threats
// ocb adjustments
// space adjustments
// activity bonus
// backward pawns
// weak squares - 5th or 6th rank
// opening - move minor pieces first then heavy pieces
// move pieces more than pawns
// weak pawn buffs - endgame
// flanks have higher scores in the endgame
// queen endgame table (strong center)
// centralize bishops in the endgame
// phased material scoring
// pawns attack the weak square
// connected passed pawns (there is existing passed pawn bonus and connected bonus)
// middlegame
// centralize pieces (via psqt)
// knight buffs when there are pawn weaknesses (mostly through a general weak square buff)
// bishops
// - defend strong square buff
// knight
// - strong square buff
// restriction bonus (given due to search / mobility scoring?)
// - via threat evals 
// weak pawns
// advanced pawns
// - advance pawns if activity advantage
// king
// - center buff
// - supporting pawns buff
// queen
// -center
// - 2nd or 3rd rank behind minor pieces buff
// connecting the rooks
// no counterparts (considered as candidate passed pawn)
// protected passed pawn (factored in)
// distanced passed pawn (factored in as part of the psqt)
// 2 bishop endgame
// - centralize king (psqt)
// - flank attacks (centralize bishops even more) (psqt)
// space advantage (center, restriction)
// blockading is assumed factored in when you're calculating against opponent's passed pawns
// opposite bishops
// - buff your diagonals
// Pawns vs Pieces
// - middlegame 3 pawns < 1 piece
// - endgame 3 pawns > 1 piece
// Pawns + Rooks vs Pieces
// - in general 1rook + 2 pawns = 2 pieces
// - Middle game  1 rook + 2 pawns < 2 pieces
// - endgame 1 rook + 2 pawns > 2 pieces
// Pawns + Pieces vs Rooks
// - in general 1 piece + 2 pawns = 1 rook
// - middle game 1 piece + 2 pawns < 1 rook
// - endgame 1 piece + 2 pawns > 1 rook
// Bishop vs rook vs knight
// - in general 1 bishop / 1 knight < 1 rook
// - endgame 1 bishop ~= 1 rook
// - endgame 1 bishop > 1 knight

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include "attacks.h"
#include "bitboards.h"
#include "board.h"
#include "evalcache.h"
#include "evaluate.h"
#include "move.h"
#include "masks.h"
#include "thread.h"
#include "transposition.h"
#include "types.h"


EvalTrace T, EmptyTrace;
int PSQT[32][SQUARE_NB];

#define S(mg, eg) (MakeScore((mg), (eg)))

/* Material Value Evaluation Terms */

const int PawnValue   = S( 100, 130);
const int KnightValue = S( 330, 330);
const int BishopValue = S( 340, 500);
const int RookValue   = S( 540, 515);
const int QueenValue  = S(1000,1000);
const int KingValue   = S(   0,   0);

/* Piece Square Evaluation Terms */


// ideas: center control, advance the center if early. advance the flanks if late.

const int PawnPSQT[SQUARE_NB] = {
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0),
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0),
    S( -10,  10), S( -10,   5), S(   0,  -5), S(  10, -15), S(  10, -15), S(   0,  -5), S( -10,   5), S( -10,  10),
    S( -10,  15), S( -10,  15), S(  10, -10), S(  20, -20), S(  20, -20), S(  10, -10), S( -10,  15), S( -10,  15),
    S( -10,  20), S( -10,  20), S(  10, -10), S(   5, -20), S(   5, -20), S(  10, -10), S( -10,  20), S( -10,  20),
    S( -20,  40), S( -10,  40), S(  10,   0), S(  30, -10), S(  30, -10), S(  10,   0), S( -10,  40), S( -20,  40),
    S( -30,  60), S( -30,   0), S(  40,   0), S(  50, -10), S(  50, -10), S(  40,   0), S( -30,   0), S( -30,  60),
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0),
};


// knight on the rim is grim
// knight on the 6th rank is generally strong
const int KnightPSQT[SQUARE_NB] = {
    S( -20, -20), S( -20, -20), S( -20, -20), S( -20, -20), S( -20, -20), S( -20, -20), S( -20, -20), S( -20, -20),
    S( -20, -20), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S( -20, -20),
    S( -20, -20), S(   5,   0), S(  10,   5), S(  15,  20), S(  15,  20), S(  10,   5), S(   5,   0), S( -20, -20),
    S( -20, -20), S(  15,  30), S(  20,  40), S(  20,  50), S(  20,  50), S(  20,  40), S(  15,  20), S( -20, -20),
    S( -20, -20), S(  20,  30), S(  30,  50), S(  30,  60), S(  30,  60), S(  30,  50), S(  20,  30), S( -20, -20),
    S( -20, -20), S(  10,  30), S(  20,  50), S(  20,  60), S(  20,  60), S(  20,  50), S(  10,  30), S( -20, -20),
    S( -20, -20), S(   5,   5), S(   5,   5), S(   5,   5), S(   5,   5), S(   5,   5), S(   5,   5), S( -20, -20),
    S(-150, -20), S(-100, -20), S(-100, -20), S( -30, -20), S( -30, -20), S(-100, -20), S(-100, -20), S(-150, -20),
};

// similar to knights where you want to center it
// but instead of knight on the 6th rank, it's center is more buffed
// 
const int BishopPSQT[SQUARE_NB] = {
    S( -20, -20), S( -10, -10), S( -10, -10), S( -10, -10), S( -10, -10), S( -10, -10), S( -10, -10), S( -20, -20),
    S( -10, -10), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S( -10, -10),
    S( -10, -10), S(   5,   0), S(  10,   5), S(  15,  15), S(  15,  15), S(  10,   5), S(   5,   0), S( -10, -10),
    S( -10, -10), S(  15,  20), S(  15,  30), S(  30,  50), S(  30,  50), S(  15,  30), S(  15,  15), S( -10, -10),
    S( -10, -10), S(  15,  20), S(  20,  30), S(  30,  50), S(  30,  50), S(  20,  30), S(  15,  20), S( -10, -10),
    S( -10, -10), S(  10,  20), S(  15,  30), S(  15,  30), S(  15,  30), S(  15,  30), S(  10,  20), S( -10, -10),
    S( -10, -10), S(   5,   5), S(   5,   5), S(   5,   5), S(   5,   5), S(   5,   5), S(   5,   5), S( -10, -10),
    S( -20, -20), S( -10, -10), S( -10, -10), S( -30, -10), S( -30, -10), S( -10, -10), S( -10, -10), S( -20, -20),
};

// opening: rook om the 7th and 8th ranks
// ending: advance the rooks, still all about the 7th and 8th ranks
const int RookPSQT[SQUARE_NB] = {
    S( -20,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S( -20,   0),
    S( -70,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S( -70,   0),
    S( -30,   0), S(   0,  10), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), S( -30,   0),
    S( -30,  20), S(   0,  30), S(   0,  30), S(   0,  20), S(   0,  20), S(   0,  30), S(   0,  30), S( -30,  20),
    S( -20,  40), S(   0,  30), S(   0,  30), S(   0,  30), S(   0,  30), S(   0,  30), S(   0,  30), S( -20,  40),
    S( -30,  40), S(   0,  40), S(   0,  40), S(   0,  30), S(   0,  30), S(   0,  30), S(   0,  30), S( -20,  40),
    S(  20,  50), S(  20,  50), S(  20,  50), S(  20,  50), S(  20,  50), S(  20,  50), S(  20,  50), S(  20,  50),
    S(  40,  50), S(  40,  50), S(  40,  50), S(  40,  50), S(  40,  50), S(  40,  50), S(  40,  50), S(  30,  50),
};

// avoid the rims like the knights and bishops
// centralize in general
// in the opening, put it on the 2nd or 3rd ranks, ideally behind rooks
const int QueenPSQT[SQUARE_NB] = {
    S( -20, -20), S( -10, -10), S( -10, -10), S( -10, -10), S( -10, -10), S( -10, -10), S( -10, -10), S( -20, -20),
    S( -10, -10), S(  20,  20), S(  20,  20), S(  20,  20), S(  20,  20), S(  20,  20), S(  20,  20), S( -10, -10),
    S( -10, -10), S(  20,  20), S(  20,  20), S(  20,  20), S(  20,  20), S(  20,  20), S(  20,  20), S( -10, -10),
    S( -10, -10), S(   0,  10), S(  10,  30), S(  30,  50), S(  30,  50), S(  10,  30), S(   0,  10), S( -10, -10),
    S( -10, -10), S(   0,  10), S(  10,  30), S(  30,  50), S(  30,  50), S(  10,  30), S(   0,  10), S( -10, -10),
    S( -10, -10), S(   0,   5), S(   5,   5), S(   5,   5), S(   5,   5), S(   5,   5), S(   0,   5), S( -10, -10),
    S( -10, -10), S(   0,   5), S(   5,   5), S(   5,   5), S(   5,   5), S(   5,   5), S(   0,   5), S( -10, -10),
    S( -20, -20), S( -10, -10), S( -10, -10), S( -30, -10), S( -30, -10), S( -10, -10), S( -10, -10), S( -20, -20),
};

// opening - stay at the backrank
// endgame - be active and move to the center
const int KingPSQT[SQUARE_NB] = {
    S(  80, -80), S(  60, -50), S(   0,   0), S( -10, -20), S( -10, -20), S(   0,   0), S(  50, -50), S(  70, -80),
    S(   0,   0), S( -20,   0), S( -40,  10), S( -40,  20), S( -40,  20), S( -40,  10), S( -20,   0), S(   0,   0),
    S( -40, -10), S( -40, -10), S( -40,  10), S( -40,  30), S( -40,  30), S( -40,  10), S( -40, -10), S( -40, -10),
    S( -40, -40), S( -40, -30), S( -40,  10), S( -40,  40), S( -40,  40), S( -40,  10), S( -40, -30), S( -40, -30),
    S( -40, -10), S( -40, -30), S( -40,  10), S( -40,  40), S( -40,  40), S( -40,  10), S( -40, -30), S( -40, -10),
    S( -40, -30), S( -40, -20), S( -40,   0), S( -40,   0), S( -40,   0), S( -40,   0), S( -40, -20), S( -40, -40),
    S( -40, -90), S( -40, -20), S( -40, -10), S( -40, -40), S( -40, -30), S( -40, -20), S( -40, -20), S( -40,-110),
    S( -40,-150), S( -40, -90), S( -40, -70), S( -40, -30), S( -40, -50), S( -40, -70), S( -40, -90), S( -40,-150),
};

/* Pawn Evaluation Terms */

// the choice between [0] or [1] is based on if there are more threats than support [0] or if there
// is more support than threats [1]. i am ambivalent, therefore i'll just use one set of values for both.
const int PawnCandidatePasser[2][RANK_NB] = {
   {S(   0,   0), S( -10, -10), S( -10,  10), S(   0,  20), S(  20,  50), S(  40,  70), S(  50,  90), S(   0,   0)},
   {S(   0,   0), S( -10, -10), S( -10,  10), S(   0,  20), S(  20,  50), S(  40,  70), S(  50,  90), S(   0,   0)},
};

// isolated pawns are weaker in the middlegame if at center
// isolated pawns are weaker in the endgame if at the edges
const int PawnIsolated[FILE_NB] = {
    S( -10, -20), S( -10, -15), S( -15, -20), S( -20, -30), S( -20, -30), S( -15, -20), S( -10, -15), S( -10, -20),
};

// the choice between [0] or [1] is based upon stoppers to passed pawns & neighbors.
// i'm ambivalent, thus they are valued similarly as isolated pawns
const int PawnStacked[2][FILE_NB] = {
   {S( -10, -20), S( -10, -20), S( -15, -20), S( -20, -30), S( -20, -30), S( -15, -25), S( -10, -20), S( -10, -20)},
   {S( -10, -20), S( -10, -20), S( -15, -20), S( -20, -30), S( -20, -30), S( -15, -25), S( -10, -20), S( -10, -20)},
};

// flag just checks if there are enemy pawns on the file
// i guess this can be construed as a counterpart bonus (i.e. no enemy pawns on the file)
// both are by rank
// this should be generally weak at the center and gradually increasing from the 2nd and 7th ranks
const int PawnBackwards[2][RANK_NB] = {
   {S(   0,   0), S(   0, -10), S(  -5, -20), S( -10, -30), S( -10, -30), S(  -5, -20), S(   0, -10), S(   0,   0)},
   {S(   0,   0), S(   0, -10), S(  -5, -20), S( -10, -30), S( -10, -30), S(  -5, -20), S(   0, -10), S(   0,   0)},
};

// the deeper they are, the stronger they should be
// should be stronger in the endgame than the midgame
// the usual flanks focus in the endgame and center focus in the middle game
const int PawnConnected32[32] = {
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), // rank 1, from edge to center
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), // rank 2, ""
    S(   0,  10), S(   5,   5), S(  10,   0), S(  10,   0), // rank 3, ""
    S(   0,  30), S(  10,  20), S(  20,  10), S(  20,  10), // rank 4, ""
    S(  10,  30), S(  20,  30), S(  30,  20), S(  30,  20), // rank 5, ""
    S(  50,  80), S(  60,  70), S(  70,  60), S(  80,  50), // rank 6, ""
    S(  70, 100), S(  80,  90), S(  90,  80), S( 100,  70), // rank 7, ""
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0), // rank 8, ""
};


/* Weak Squares */
// [0] means that the weak square is not at the rim
// [1] means the weak square are at the rims
// TODO: add in tuner
const int WeakSquareAttackedByPawn[2] = {
   S(   2,   2),
   S(   0,   0), 
};

const int WeakSquareAttackedByKnight[2] = {
   S(  20,  10), 
   S(   0,   0),
};

const int WeakSquareAttackedByBishop[2] = {
   S(  40,  20), 
   S(   0,   0), 
};

const int WeakSquareAttackedByRook[2] = {
    S(   4,  4),
};

const int WeakSquareAttackedByQueen[2] = {
    S(   4,  4),
};

const int AvailableWeakSquare[2] = {
   S(   4,   2), 
   S(   0,   0),
};


/* Knight Evaluation Terms */

// [0] means that the outpost is not at the rim
// [1] means the outpost are at the rims
const int KnightOutpost[2][2] = {
   {S(  40,  20), S(  40,   20)}, 
   {S( -10, -10), S( -10,  -10)},
};

// const int KnightBehindPawn = S(   5,  30);

// const int KnightInSiberia[4] = {
//     S(   0,   0), S( -10, -20), S( -20, -20), S( -40, -40),
// };

// simply checks how many squares can it attack
const int KnightMobility[9] = {
    S(-150,-150), S( -100,-100), S( -50, -50), S(   0,   0), S(  10,  10), S(  30,  30), S(  30,  30), S(  30,  30), S(  50,  50),
};

/* Bishop Evaluation Terms */

const int BishopPair = S(  30, 120);

const int BishopRammedPawns = S(  -5, -20);

// const int BishopOutpost[2][2] = {
//    {S(  10, -10), S(  50,  -5)}, {S(   0, -5), S(  0,  -5)},
// };

// const int BishopBehindPawn = S(   5,  20);

const int BishopLongDiagonal = S(  20,  0);

// more squares mean it's more centralized
const int BishopMobility[2][14] = {
    {S( -150,-150), S( -120,-120), S( -50, -50), S( -20, -20), S(   0,   0), S(  10,  10), S(  30,  30), S(  30,  30),
    S(  40,  40), S(  40,  40), S(  40,  40), S(  40,  40), S(  50,  50), S(  80,  80)},
    {S( -120,-120), S( -100,-100), S( -20, -20), S( -10, -10), S(  10,  10), S(  20,  20), S(  50,  50), S(  50,  50),
    S(  60,  60), S(  70,  70), S(  80,  80), S(  80,  80), S(  90,  90), S(  100,  100)},
};

/* Rook Evaluation Terms */

const int RookFile[2] = { S(  10,  10), S(  10,  10) };

// const int RookOnSeventh = S(   5,  40);

// mobility isn't as important in the opening-middlegame
const int RookMobility[15] = {
    S(-150,-150), S(-120,-120), S( -80, -80), S( -20, -20), S(   0,   0), S(   0,  20), S(   0,  40), S(   0,  40),
    S(   0,  50), S(   0,  50), S(  10,  60), S(  10,  60), S(  10,  70), S(  30,  70), S(  90,  90),
};

// 
const int ConnectedRooks = S(  10,  20);

/* Queen Evaluation Terms */

const int QueenRelativePin = S( -20, -20);

// more squares mean it's more centralized
const int QueenMobility[28] = {
    S(-150,-150), S(-120,-120), S(-120,-220), S( -40,-200), S( -20,-170), S(   0, -80), S(   0, -30), S(   0,   0),
    S(   0,   0), S(  10,  30), S(  10,  30), S(  10,  50), S(  20,  50), S(  20,  50), S(  20,  50), S(  20,  60),
    S(  20,  60), S(  10,  60), S(  10,  60), S(  10,  40), S(  20,  30), S(  30,   0), S(  30, -10), S(  20, -20),
    S(  10, -40), S(   0, -70), S( -40, -70), S( -40, -70),
};

/* King Evaluation Terms */

const int KingDefenders[12] = {
    S( -30,  -5), S( -10,   5), S(   0,   5), S(  10,   5),
    S(  20,   5), S(  30,   5), S(  30, -15), S(  10,  -5),
    S(  10,   5), S(  10,   5), S(  10,   5), S(  10,   5),
};

const int KingPawnFileProximity[FILE_NB] = {
    S(  30,  40), S(  20,  30), S(  10,  10), S(   0, -20),
    S(   0, -60), S(   0, -70), S( -10, -80), S( -10, -70),
};

const int KingShelter[2][FILE_NB][RANK_NB] = {
  {{S(   0,   0), S(  10, -30), S(  20,   0), S(  20,   0),
    S(   0,   0), S( -10,   0), S( -10, -30), S( -50,  20)},
   {S(  10,   0), S(   0, -10), S(   0,   0), S(   0,   0),
    S( -10,   0), S( -50,  70), S(  80,  80), S( -10,   0)},
   {S(  30,   0), S(   0,   0), S( -30,   0), S( -10, -10),
    S(   0,   0), S( -20,  10), S(  10,  70), S( -10,   0)},
   {S(  10,  10), S(  20, -10), S(   0, -10), S(  10, -20),
    S(  20, -30), S( -40,   0), S(-140,  40), S(   0,   0)},
   {S( -10,  10), S(   0,   0), S( -40,   0), S( -20,  10),
    S( -20,   0), S( -30,   0), S(  40, -20), S( -10,   0)},
   {S(  50, -10), S(  10, -10), S( -20,   0), S( -10, -20),
    S(  10, -30), S(  30, -20), S(  40, -30), S( -20,   0)},
   {S(  40, -10), S(   0, -20), S( -30,   0), S( -20,   0),
    S( -30,   0), S( -20,  20), S(   0,  40), S( -10,   0)},
   {S(  10, -20), S(   0, -20), S(  10,   0), S(   0,  10),
    S( -10,  20), S( -10,  40), S(-180,  80), S( -10,  10)}},
  {{S(   0,   0), S( -10, -30), S(   0, -20), S( -40,  10),
    S( -30,   0), S(   0,  50), S(-160,   0), S( -50,  10)},
   {S(   0,   0), S(  10, -10), S(   0, -10), S( -10,   0),
    S(   0, -20), S(  20,  70), S(-180,   0), S( -30,  10)},
   {S(   0,   0), S(  10,   0), S(   0, -10), S(   0, -20),
    S(  20,   0), S( -90,  50), S( -80, -70), S(   0,   0)},
   {S(   0,   0), S(   0,   0), S(   0,   0), S( -30,  10),
    S( -40,  10), S( -90,  30), S(   0, -40), S( -30,   0)},
   {S(   0,   0), S(  10,   0), S(  10, -10), S(  10, -10),
    S(   0, -10), S( -30,   0), S(-100, -50), S( -10,   0)},
   {S(   0,   0), S(   0,   0), S( -20,   0), S( -10,   0),
    S(  20, -20), S( -20,  10), S(  50,  30), S( -10,   0)},
   {S(   0,   0), S(  30, -20), S(  10, -10), S(   0,   0),
    S( -20,  10), S(   0,  20), S( -50, -30), S( -20,  10)},
   {S(   0,   0), S(  10, -50), S(  10, -30), S( -10,   0),
    S( -30,  20), S( -10,  20), S(-220, -40), S( -30,   0)}},
};

const int KingStorm[2][FILE_NB/2][RANK_NB] = {
  {{S(   0,  30), S( 140,   0), S( -10,  20), S(   0,   0),
    S( -10,   0), S(   0,   0), S( -10,   0), S( -20,   0)},
   {S( -10,  60), S(  60,  10), S(   0,  20), S(   0,  10),
    S(   0,   0), S(   0,   0), S(   0,   0), S( -10,   0)},
   {S(   0,  40), S(  10,  30), S( -10,  20), S( -10,  10),
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0)},
   {S(   0,  20), S(  10,  20), S( -30,  10), S( -20,   0),
    S( -10,   0), S(  10, -10), S(   0,   0), S( -20,   0)}},
  {{S(   0,   0), S( -10, -10), S( -10,   0), S(  20, -20),
    S(  10,   0), S(  10, -20), S(   0,   0), S(   0,  30)},
   {S(   0,   0), S( -10, -40), S(   0, -10), S(  50, -10),
    S(  10,   0), S(  20, -20), S( -10, -10), S( -30,   0)},
   {S(   0,   0), S( -30, -60), S( -10, -10), S(   0,   0),
    S(   0,   0), S(   0, -10), S(   0, -20), S(   0,   0)},
   {S(   0,   0), S(   0, -20), S( -20, -10), S( -20,   0),
    S( -10,   0), S(   0, -30), S(  60, -20), S(  10,  20)}},
};

/* Safety Evaluation Terms */

const int SafetyKnightWeight    = S(  40,  40);
const int SafetyBishopWeight    = S(  20,  30);
const int SafetyRookWeight      = S(  30,   0);
const int SafetyQueenWeight     = S(  30,   0);

const int SafetyAttackValue     = S(  40,  30);
const int SafetyWeakSquares     = S(  40,  40);
const int SafetyNoEnemyQueens   = S(-230,-250);
const int SafetySafeQueenCheck  = S(  90,  80);
const int SafetySafeRookCheck   = S(  90,  90);
const int SafetySafeBishopCheck = S(  50,  50);
const int SafetySafeKnightCheck = S( 110, 110);
const int SafetyAdjustment      = S( -70, -20);

const int SafetyShelter[2][RANK_NB] = {
   {S(   0,   0), S(   0,  10), S(   0,   0), S(   0,   0),
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0, -10)},
   {S(   0,   0), S(   0,  10), S(   0,   0), S(   0,   0),
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0)},
};

const int SafetyStorm[2][RANK_NB] = {
   {S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0),
    S(   0,   0), S(   0,  20), S(   0,  10), S(   0, -10)},
   {S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0),
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,   0)},
};

/* Passed Pawn Evaluation Terms */

const int PassedPawn[2][2][RANK_NB] = {
  {{S(   0,   0), S( -30,   0), S( -40,  20), S( -60,  20),
    S(   0,  10), S(  90,   0), S( 160,  40), S(   0,   0)},
   {S(   0,   0), S( -20,  10), S( -40,  40), S( -50,  40),
    S(   0,  50), S( 110,  50), S( 190,  90), S(   0,   0)}},
  {{S(   0,   0), S( -20,  20), S( -40,  30), S( -60,  50),
    S(   0,  60), S( 100,  70), S( 250, 120), S(   0,   0)},
   {S(   0,   0), S( -20,  20), S( -40,  30), S( -50,  60),
    S(   0,  80), S(  90, 160), S( 120, 290), S(   0,   0)}},
};

const int PassedFriendlyDistance[FILE_NB] = {
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0, -10),
    S(   0, -10), S(   0, -10), S(   0,   0), S(   0,   0),
};

const int PassedEnemyDistance[FILE_NB] = {
    S(   0,   0), S(   0,   0), S(   0,   0), S(   0,  10),
    S(   0,  20), S(   0,  30), S(  10,  30), S(   0,   0),
};

const int PassedSafePromotionPath = S( -40,  50);

/* Threat Evaluation Terms */

// always should be by a lesser piece as a principle
// on weak pawn, we assume that it's non-orthogonal with isolated pawns, etc

const int ThreatWeakPawn             = S( -10, -40);
const int ThreatMinorAttackedByPawn  = S( -20, -40);
// const int ThreatMinorAttackedByMinor = S( -20, -40);
// const int ThreatMinorAttackedByMajor = S( -30, -50);
const int ThreatRookAttackedByLesser = S( -20, -40);
// const int ThreatMinorAttackedByKing  = S( -40, -20);
// const int ThreatRookAttackedByKing   = S( -30, -10);
const int ThreatQueenAttackedByOne   = S( -20, -40);
// const int ThreatOverloadedPieces     = S(   0, -10);
// const int ThreatByPawnPush           = S(  10,  30);

/* Space Evaluation Terms */

// penalties
const int SpaceRestrictPiece = S( -30, -50);
const int SpaceRestrictEmpty = S( -10, -30);

// bonus
const int SpaceCenterControl = S(  40,   0);

/* Closedness Evaluation Terms */

const int ClosednessKnightAdjustment[9] = {
    S(   0,  10), S(   0,  20), S(   0,  30), S(   0,  30),
    S(   0,  40), S(   0,  30), S(   0,  30), S( -10,  50),
    S(   0,  30),
};

const int ClosednessRookAdjustment[9] = {
    S(  40,  40), S(   0,  80), S(   0,  50), S(   0,  40),
    S(   0,  40), S(   0,  20), S(   0,  10), S( -10,  10),
    S( -30, -10),
};

/* Complexity Evaluation Terms */

const int ComplexityTotalPawns  = S(   0,   0);
const int ComplexityPawnFlanks  = S(   0,  80);
const int ComplexityPawnEndgame = S(   0,  70);
const int ComplexityAdjustment  = S(   0,-150);

/* General Evaluation Terms */

const int Tempo = 20;

#undef S

int evaluateBoard(Thread *thread, Board *board) {

    EvalInfo ei;
    int phase, factor, eval, pkeval, hashed;

    // We can recognize positions we just evaluated
    if (thread->moveStack[thread->height-1] == NULL_MOVE)
        return -thread->evalStack[thread->height-1] + 2 * Tempo;

    // Check for this evaluation being cached already
    if (!TRACE && getCachedEvaluation(thread, board, &hashed))
        return hashed;

    initEvalInfo(thread, board, &ei);
    eval = evaluatePieces(&ei, board);

    pkeval = ei.pkeval[WHITE] - ei.pkeval[BLACK];;
    eval += pkeval + board->psqtmat;
    eval += evaluateClosedness(&ei, board);
    eval += evaluateComplexity(&ei, board, eval);


    // Calculate the game phase based on remaining material (Fruit Method)
    phase = 24 - 4 * popcount(board->pieces[QUEEN ])
               - 2 * popcount(board->pieces[ROOK  ])
               - 1 * popcount(board->pieces[KNIGHT]
                             |board->pieces[BISHOP]);
    phase = (phase * 256 + 12) / 24;

    // Scale evaluation based on remaining material
    factor = evaluateScaleFactor(board, eval);
    if (TRACE) T.factor = factor;

    // Compute and store an interpolated evaluation from white's POV
    eval = (ScoreMG(eval) * (256 - phase)
         +  ScoreEG(eval) * phase * factor / SCALE_NORMAL) / 256;
    storeCachedEvaluation(thread, board, eval);

    // Store a new Pawn King Entry if we did not have one
    if (!TRACE && ei.pkentry == NULL)
        storeCachedPawnKingEval(thread, board, ei.passedPawns, pkeval, ei.pksafety[WHITE], ei.pksafety[BLACK]);

    // Factor in the Tempo after interpolation and scaling, so that
    // if a null move is made, then we know eval = last_eval + 2 * Tempo
    return Tempo + (board->turn == WHITE ? eval : -eval);
}

int evaluatePieces(EvalInfo *ei, Board *board) {

    int eval;

    eval  =   evaluatePawns(ei, board, WHITE)   - evaluatePawns(ei, board, BLACK);

    // This needs to be done after pawn evaluation but before king safety evaluation
    evaluateKingsPawns(ei, board, WHITE);
    evaluateKingsPawns(ei, board, BLACK);

    eval += evaluateKnights(ei, board, WHITE) - evaluateKnights(ei, board, BLACK);
    eval += evaluateBishops(ei, board, WHITE) - evaluateBishops(ei, board, BLACK);
    eval +=   evaluateRooks(ei, board, WHITE)   - evaluateRooks(ei, board, BLACK);
    eval +=  evaluateQueens(ei, board, WHITE)  - evaluateQueens(ei, board, BLACK);
    eval +=   evaluateKings(ei, board, WHITE)   - evaluateKings(ei, board, BLACK);
    eval +=  evaluatePassed(ei, board, WHITE)  - evaluatePassed(ei, board, BLACK);
    eval += evaluateThreats(ei, board, WHITE) - evaluateThreats(ei, board, BLACK);
    eval +=   evaluateSpace(ei, board, WHITE) -   evaluateSpace(ei, board, BLACK);

    return eval;
}

int evaluatePawns(EvalInfo *ei, Board *board, int colour) {

    const int US = colour, THEM = !colour;
    const int Forward = (colour == WHITE) ? 8 : -8;

    int sq, flag, outside, eval = 0, pkeval = 0;
    uint64_t pawns, myPawns, tempPawns, enemyPawns, attacks;

    // Store off pawn attacks for king safety and threat computations
    ei->attackedBy2[US]      = ei->pawnAttacks[US] & ei->attacked[US];
    ei->attacked[US]        |= ei->pawnAttacks[US];
    ei->attackedBy[US][PAWN] = ei->pawnAttacks[US];

    // Update King Safety calculations
    attacks = ei->pawnAttacks[US] & ei->kingAreas[THEM];
    ei->kingAttacksCount[THEM] += popcount(attacks);

    // Pawn hash holds the rest of the pawn evaluation
    if (ei->pkentry != NULL) return eval;

    pawns = board->pieces[PAWN];
    myPawns = tempPawns = pawns & board->colours[US];
    enemyPawns = pawns & board->colours[THEM];

    // Evaluate each pawn (but not for being passed)
    while (tempPawns) {

        // Pop off the next pawn
        sq = poplsb(&tempPawns);
        if (TRACE) T.PawnValue[US]++;
        if (TRACE) T.PawnPSQT[relativeSquare(US, sq)][US]++;

        uint64_t neighbors   = myPawns    & adjacentFilesMasks(fileOf(sq));
        uint64_t backup      = myPawns    & passedPawnMasks(THEM, sq);
        uint64_t stoppers    = enemyPawns & passedPawnMasks(US, sq);
        // pawn threats quantity (us)
        uint64_t threats     = enemyPawns & pawnAttacks(US, sq);
        // pawn support quantity
        uint64_t support     = myPawns    & pawnAttacks(THEM, sq);
        uint64_t pushThreats = enemyPawns & pawnAttacks(US, sq + Forward);
        uint64_t pushSupport = myPawns    & pawnAttacks(THEM, sq + Forward);
        uint64_t leftovers   = stoppers ^ threats ^ pushThreats;

        // Save passed pawn information for later evaluation
        if (!stoppers) setBit(&ei->passedPawns, sq);

        // Apply a bonus for pawns which will become passers by advancing a
        // square then exchanging our supporters with the remaining stoppers
        else if (!leftovers && popcount(pushSupport) >= popcount(pushThreats)) {
            // popcount = Returns the number of 1 bits in the value of x.
            // returns 0 if false, 1 if true
            // if there is more or equal pawn support than threats, then use 1
            // else use 0
            flag = popcount(support) >= popcount(threats);
            pkeval += PawnCandidatePasser[flag][relativeRankOf(US, sq)];
            if (TRACE) T.PawnCandidatePasser[flag][relativeRankOf(US, sq)][US]++;
        }

        // Apply a penalty if the pawn is isolated. We consider pawns that
        // are able to capture another pawn to not be isolated, as they may
        // have the potential to deisolate by capturing, or be traded away
        if (!threats && !neighbors) {
            pkeval += PawnIsolated[fileOf(sq)];
            if (TRACE) T.PawnIsolated[fileOf(sq)][US]++;
        }

        // Apply a penalty if the pawn is stacked. We adjust the bonus for when
        // the pawn appears to be a candidate to unstack. This occurs when the
        // pawn is not passed but may capture or be recaptured by our own pawns,
        // and when the pawn may freely advance on a file and then be traded away
        if (several(Files[fileOf(sq)] & myPawns)) {
            flag = (stoppers && (threats || neighbors))
                || (stoppers & ~forwardFileMasks(US, sq));
            pkeval += PawnStacked[flag][fileOf(sq)];
            if (TRACE) T.PawnStacked[flag][fileOf(sq)][US]++;
        }

        // Apply a penalty if the pawn is backward. We follow the usual definition
        // of backwards, but also specify that the pawn is not both isolated and
        // backwards at the same time. We don't give backward pawns a connected bonus
        if (neighbors && pushThreats && !backup) {
            flag = !(Files[fileOf(sq)] & enemyPawns);
            pkeval += PawnBackwards[flag][relativeRankOf(US, sq)];
            if (TRACE) T.PawnBackwards[flag][relativeRankOf(US, sq)][US]++;
        }

        // Apply a bonus if the pawn is connected and not backwards. We consider a
        // pawn to be connected when there is a pawn lever or the pawn is supported
        else if (pawnConnectedMasks(US, sq) & myPawns) {
            // relative square 32 is a vertically sliced board
            // etc
            //  8  9 10 11 11 10  9  8
            //  4  5  6  7  7  6  5  4
            //  0  1  2  3  3  2  1  0
            pkeval += PawnConnected32[relativeSquare32(US, sq)];
            if (TRACE) T.PawnConnected32[relativeSquare32(US, sq)][US]++;
        }

        // weak square attack bonus
        if (!(outpostSquareMasks(US, sq) & enemyPawns) && ei->pawnAttacks[US]) {
          outside  = testBit(FILE_A | FILE_H, sq);
          pkeval += WeakSquareAttackedByPawn[outside];
        }
        
    }

    ei->pkeval[US] = pkeval; // Save eval for the Pawn Hash

    return eval;
}

int evaluateKnights(EvalInfo *ei, Board *board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, defended, outside, count, eval = 0;
    uint64_t attacks;

    uint64_t enemyPawns  = board->pieces[PAWN  ] & board->colours[THEM];
    uint64_t tempKnights = board->pieces[KNIGHT] & board->colours[US  ];

    ei->attackedBy[US][KNIGHT] = 0ull;

    // Evaluate each knight
    while (tempKnights) {

        // Pop off the next knight
        sq = poplsb(&tempKnights);
        if (TRACE) T.KnightValue[US]++;
        if (TRACE) T.KnightPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        attacks = knightAttacks(sq);
        ei->attackedBy2[US]        |= attacks & ei->attacked[US];
        ei->attacked[US]           |= attacks;
        ei->attackedBy[US][KNIGHT] |= attacks;

        // Apply a bonus if the knight is on an outpost square, and cannot be attacked
        // by an enemy pawn. Increase the bonus if one of our pawns supports the knight

        // small bonus if a weak square is defended by the knight

        // very small bonus if a weak square is available
        if (testBit(outpostRanksMasks(US), sq) && !(outpostSquareMasks(US, sq) & enemyPawns)
            ) {
            outside  = testBit(FILE_A | FILE_H, sq);
            defended = testBit(ei->pawnAttacks[US], sq);
            eval += KnightOutpost[outside][defended];
            if (TRACE) T.KnightOutpost[outside][defended][US]++;
        } else if (!(outpostSquareMasks(US, sq) & enemyPawns) && attacks) {
          outside  = testBit(FILE_A | FILE_H, sq);
          eval += WeakSquareAttackedByKnight[outside];
        } else if (!(outpostSquareMasks(US, sq) & enemyPawns)) {
          outside  = testBit(FILE_A | FILE_H, sq);
          eval += AvailableWeakSquare[outside];
        }

        // Apply a bonus if the knight is behind a pawn
        // if (testBit(pawnAdvance(board->pieces[PAWN], 0ull, THEM), sq)) {
        //     eval += KnightBehindPawn;
        //     if (TRACE) T.KnightBehindPawn[US]++;
        // }

        // Apply a penalty if the knight is far from both kings
        // kingDistance = MIN(distanceBetween(sq, ei->kingSquare[THEM]), distanceBetween(sq, ei->kingSquare[US]));
        // if (kingDistance >= 4) {
        //     eval += KnightInSiberia[kingDistance - 4];
        //     if (TRACE) T.KnightInSiberia[kingDistance - 4][US]++;
        // }

        // Apply a bonus (or penalty) based on the mobility of the knight
        // 3 at the starting position
        count = popcount(ei->mobilityAreas[US] & attacks);
        eval += KnightMobility[count];
        if (TRACE) T.KnightMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyKnightWeight;
            if (TRACE) T.SafetyKnightWeight[THEM]++;
        }
    }

    return eval;
}

int evaluateBishops(EvalInfo *ei, Board *board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, count, outside, flag, eval = 0;
    uint64_t attacks;

    uint64_t enemyPawns  = board->pieces[PAWN  ] & board->colours[THEM];
    uint64_t tempBishops = board->pieces[BISHOP] & board->colours[US  ];
    uint64_t myBishops = board->pieces[BISHOP] & board->colours[US  ];
    uint64_t enemyBishops = board->pieces[BISHOP] & board->colours[THEM];

    ei->attackedBy[US][BISHOP] = 0ull;

    // Apply a bonus for having a pair of bishops
    if ((tempBishops & WHITE_SQUARES) && (tempBishops & BLACK_SQUARES)) {
        eval += BishopPair;
        if (TRACE) T.BishopPair[US]++;
    }



    // Evaluate each bishop
    while (tempBishops) {

        // Pop off the next Bishop
        sq = poplsb(&tempBishops);
        if (TRACE) T.BishopValue[US]++;
        if (TRACE) T.BishopPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        attacks = bishopAttacks(sq, ei->occupiedMinusBishops[US]);
        ei->attackedBy2[US]        |= attacks & ei->attacked[US];
        ei->attacked[US]           |= attacks;
        ei->attackedBy[US][BISHOP] |= attacks;

        // Apply a penalty for the bishop based on number of rammed pawns
        // of our own colour, which reside on the same shade of square as the bishop
        count = popcount(ei->rammedPawns[US] & squaresOfMatchingColour(sq));
        eval += count * BishopRammedPawns;
        if (TRACE) T.BishopRammedPawns[US] += count;

        // bonus if a weak square is defended by the bishop
        // very small bonus if a weak square is available
        if (!(outpostSquareMasks(US, sq) & enemyPawns) && attacks) {
          outside  = testBit(FILE_A | FILE_H, sq);
          eval += WeakSquareAttackedByBishop[outside];
        }

        // Apply a bonus if the bishop is on an outpost square, and cannot be attacked
        // by an enemy pawn. Increase the bonus if one of our pawns supports the bishop.
        // if (     testBit(outpostRanksMasks(US), sq)
        //     && !(outpostSquareMasks(US, sq) & enemyPawns)) {
        //     outside  = testBit(FILE_A | FILE_H, sq);
        //     defended = testBit(ei->pawnAttacks[US], sq);
        //     eval += BishopOutpost[outside][defended];
        //     if (TRACE) T.BishopOutpost[outside][defended][US]++;
        // }

        // Apply a bonus if the bishop is behind a pawn
        // if (testBit(pawnAdvance(board->pieces[PAWN], 0ull, THEM), sq)) {
        //     eval += BishopBehindPawn;
        //     if (TRACE) T.BishopBehindPawn[US]++;
        // }

        // Apply a bonus when controlling both central squares on a long diagonal
        if (   testBit(LONG_DIAGONALS & ~CENTER_SQUARES, sq)
            && several(bishopAttacks(sq, board->pieces[PAWN]) & CENTER_SQUARES)) {
            eval += BishopLongDiagonal;
            if (TRACE) T.BishopLongDiagonal[US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the bishop
        // mobility scores are stronger if it's OCB
        if (
            ((myBishops & WHITE_SQUARES) && (enemyBishops & BLACK_SQUARES) && (popcount(myBishops) == 1) && (popcount(enemyBishops) == 1)) || 
            ((myBishops & BLACK_SQUARES) && (enemyBishops & WHITE_SQUARES) && (popcount(myBishops) == 1) && (popcount(enemyBishops) == 1))
            ) {
          flag = 1;
          count = popcount(ei->mobilityAreas[US] & attacks);
          eval += BishopMobility[flag][count];
          if (TRACE) T.BishopMobility[count][US]++;
        } else {
          flag = 0;
          count = popcount(ei->mobilityAreas[US] & attacks);
          eval += BishopMobility[flag][count];
          if (TRACE) T.BishopMobility[count][US]++;
        }


        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyBishopWeight;
            if (TRACE) T.SafetyBishopWeight[THEM]++;
        }
    }

    return eval;
}

int evaluateRooks(EvalInfo *ei, Board *board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, open, outside, count, eval = 0;
    int last_sq = 65;
    uint64_t attacks, otherAttacks;

    uint64_t myPawns    = board->pieces[PAWN] & board->colours[  US];
    uint64_t enemyPawns = board->pieces[PAWN] & board->colours[THEM];
    uint64_t tempRooks  = board->pieces[ROOK] & board->colours[  US];
    uint64_t myRooks  = board->pieces[ROOK] & board->colours[  US];

    ei->attackedBy[US][ROOK] = 0ull;

    // Evaluate each rook
    while (tempRooks) {

        // Pop off the next rook
        sq = poplsb(&tempRooks);
        if (TRACE) T.RookValue[US]++;
        if (TRACE) T.RookPSQT[relativeSquare(US, sq)][US]++;



        // Compute possible attacks and store off information for king safety
        attacks = rookAttacks(sq, ei->occupiedMinusRooks[US]);
        ei->attackedBy2[US]      |= attacks & ei->attacked[US];
        ei->attacked[US]         |= attacks;
        ei->attackedBy[US][ROOK] |= attacks;

        // bonus if a weak square is defended by the rook
        if (!(outpostSquareMasks(US, sq) & enemyPawns) && attacks) {
          outside  = testBit(FILE_A | FILE_H, sq);
          eval += WeakSquareAttackedByRook[outside];
        }

        // Rook is on a semi-open file if there are no pawns of the rook's
        // colour on the file. If there are no pawns at all, it is an open file
        if (!(myPawns & Files[fileOf(sq)])) {
            open = !(enemyPawns & Files[fileOf(sq)]);
            eval += RookFile[open];
            if (TRACE) T.RookFile[open][US]++;
        }

        // connected rooks
        if (last_sq != 65) {
          if (testBit(myRooks, last_sq) && testBit(myRooks, sq)) {
            for(int rook_index = popcount(myRooks); rook_index > 0; --rook_index) {
              otherAttacks = rookAttacks(last_sq, ei->occupiedMinusRooks[US]);
              if((attacks & otherAttacks) != 0) {
                eval += ConnectedRooks;
              }
            }
          }
        } 

        // save the square for future reference
        last_sq = sq;

        // removed as it's a double count of the psqt
        // Rook gains a bonus for being located on seventh rank relative to its
        // colour so long as the enemy king is on the last two ranks of the board
        // if (   relativeRankOf(US, sq) == 6
        //     && relativeRankOf(US, ei->kingSquare[THEM]) >= 6) {
        //     eval += RookOnSeventh;
        //     if (TRACE) T.RookOnSeventh[US]++;
        // }

        // Apply a bonus (or penalty) based on the mobility of the rook
        count = popcount(ei->mobilityAreas[US] & attacks);
        eval += RookMobility[count];
        if (TRACE) T.RookMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyRookWeight;
            if (TRACE) T.SafetyRookWeight[THEM]++;
        }
    }

    return eval;
}

int evaluateQueens(EvalInfo *ei, Board *board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, outside, count, eval = 0;
    uint64_t tempQueens, attacks, occupied;

    uint64_t enemyPawns = board->pieces[PAWN] & board->colours[THEM];

    tempQueens = board->pieces[QUEEN] & board->colours[US];
    occupied = board->colours[WHITE] | board->colours[BLACK];

    ei->attackedBy[US][QUEEN] = 0ull;

    // Evaluate each queen
    while (tempQueens) {

        // Pop off the next queen
        sq = poplsb(&tempQueens);
        if (TRACE) T.QueenValue[US]++;
        if (TRACE) T.QueenPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        attacks = queenAttacks(sq, occupied);
        ei->attackedBy2[US]       |= attacks & ei->attacked[US];
        ei->attacked[US]          |= attacks;
        ei->attackedBy[US][QUEEN] |= attacks;

        // bonus if a weak square is defended by the queen
        if (!(outpostSquareMasks(US, sq) & enemyPawns) && attacks) {
          outside  = testBit(FILE_A | FILE_H, sq);
          eval += WeakSquareAttackedByQueen[outside];
        }

        // Apply a penalty if the Queen is at risk for a discovered attack
        if (discoveredAttacks(board, sq, US)) {
            eval += QueenRelativePin;
            if (TRACE) T.QueenRelativePin[US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the queen
        count = popcount(ei->mobilityAreas[US] & attacks);
        eval += QueenMobility[count];
        if (TRACE) T.QueenMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyQueenWeight;
            if (TRACE) T.SafetyQueenWeight[THEM]++;
        }
    }

    return eval;
}

int evaluateKingsPawns(EvalInfo *ei, Board *board, int colour) {
    // Skip computations if results are cached in the Pawn King Table
    if (ei->pkentry != NULL) return 0;

    const int US = colour, THEM = !colour;

    int dist, blocked;

    uint64_t myPawns     = board->pieces[PAWN ] & board->colours[  US];
    uint64_t enemyPawns  = board->pieces[PAWN ] & board->colours[THEM];

    int kingSq = ei->kingSquare[US];

    // Evaluate based on the number of files between our King and the nearest
    // file-wise pawn. If there is no pawn, kingPawnFileDistance() returns the
    // same distance for both sides causing this evaluation term to be neutral
    dist = kingPawnFileDistance(board->pieces[PAWN], kingSq);
    ei->pkeval[US] += KingPawnFileProximity[dist];
    if (TRACE) T.KingPawnFileProximity[dist][US]++;

    // Evaluate King Shelter & King Storm threat by looking at the file of our King,
    // as well as the adjacent files. When looking at pawn distances, we will use a
    // distance of 7 to denote a missing pawn, since distance 7 is not possible otherwise.
    for (int file = MAX(0, fileOf(kingSq) - 1); file <= MIN(FILE_NB - 1, fileOf(kingSq) + 1); file++) {

        // Find closest friendly pawn at or above our King on a given file
        uint64_t ours = myPawns & Files[file] & forwardRanksMasks(US, rankOf(kingSq));
        int ourDist = !ours ? 7 : abs(rankOf(kingSq) - rankOf(backmost(US, ours)));

        // Find closest enemy pawn at or above our King on a given file
        uint64_t theirs = enemyPawns & Files[file] & forwardRanksMasks(US, rankOf(kingSq));
        int theirDist = !theirs ? 7 : abs(rankOf(kingSq) - rankOf(backmost(US, theirs)));

        // Evaluate King Shelter using pawn distance. Use separate evaluation
        // depending on the file, and if we are looking at the King's file
        ei->pkeval[US] += KingShelter[file == fileOf(kingSq)][file][ourDist];
        if (TRACE) T.KingShelter[file == fileOf(kingSq)][file][ourDist][US]++;

        // Update the Shelter Safety
        ei->pksafety[US] += SafetyShelter[file == fileOf(kingSq)][ourDist];
        if (TRACE) T.SafetyShelter[file == fileOf(kingSq)][ourDist][US]++;

        // Evaluate King Storm using enemy pawn distance. Use a separate evaluation
        // depending on the file, and if the opponent's pawn is blocked by our own
        blocked = (ourDist != 7 && (ourDist == theirDist - 1));
        ei->pkeval[US] += KingStorm[blocked][mirrorFile(file)][theirDist];
        if (TRACE) T.KingStorm[blocked][mirrorFile(file)][theirDist][US]++;

        // Update the Storm Safety
        ei->pksafety[US] += SafetyStorm[blocked][theirDist];
        if (TRACE) T.SafetyStorm[blocked][theirDist][US]++;
    }

    return 0;
}

int evaluateKings(EvalInfo *ei, Board *board, int colour) {

    const int US = colour, THEM = !colour;

    int count, safety, mg, eg, eval = 0;

    uint64_t enemyQueens = board->pieces[QUEEN] & board->colours[THEM];

    uint64_t defenders  = (board->pieces[PAWN  ] & board->colours[US])
                        | (board->pieces[KNIGHT] & board->colours[US])
                        | (board->pieces[BISHOP] & board->colours[US]);

    int kingSq = ei->kingSquare[US];
    if (TRACE) T.KingValue[US]++;
    if (TRACE) T.KingPSQT[relativeSquare(US, kingSq)][US]++;

    // Bonus for our pawns and minors sitting within our king area
    count = popcount(defenders & ei->kingAreas[US]);
    eval += KingDefenders[count];
    if (TRACE) T.KingDefenders[count][US]++;

    // Perform King Safety when we have two attackers, or
    // one attacker with a potential for a Queen attacker
    if (ei->kingAttackersCount[US] > 1 - popcount(enemyQueens)) {

        // Weak squares are attacked by the enemy, defended no more
        // than once and only defended by our Queens or our King
        uint64_t weak =   ei->attacked[THEM]
                      &  ~ei->attackedBy2[US]
                      & (~ei->attacked[US] | ei->attackedBy[US][QUEEN] | ei->attackedBy[US][KING]);

        // Usually the King Area is 9 squares. Scale are attack counts to account for
        // when the king is in an open area and expects more attacks, or the opposite
        int scaledAttackCounts = 9.0 * ei->kingAttacksCount[US] / popcount(ei->kingAreas[US]);

        // Safe target squares are defended or are weak and attacked by two.
        // We exclude squares containing pieces which we cannot capture.
        uint64_t safe =  ~board->colours[THEM]
                      & (~ei->attacked[US] | (weak & ei->attackedBy2[THEM]));

        // Find square and piece combinations which would check our King
        uint64_t occupied      = board->colours[WHITE] | board->colours[BLACK];
        uint64_t knightThreats = knightAttacks(kingSq);
        uint64_t bishopThreats = bishopAttacks(kingSq, occupied);
        uint64_t rookThreats   = rookAttacks(kingSq, occupied);
        uint64_t queenThreats  = bishopThreats | rookThreats;

        // Identify if there are pieces which can move to the checking squares safely.
        // We consider forking a Queen to be a safe check, even with our own Queen.
        uint64_t knightChecks = knightThreats & safe & ei->attackedBy[THEM][KNIGHT];
        uint64_t bishopChecks = bishopThreats & safe & ei->attackedBy[THEM][BISHOP];
        uint64_t rookChecks   = rookThreats   & safe & ei->attackedBy[THEM][ROOK  ];
        uint64_t queenChecks  = queenThreats  & safe & ei->attackedBy[THEM][QUEEN ];

        safety  = ei->kingAttackersWeight[US];

        safety += SafetyAttackValue     * scaledAttackCounts
                + SafetyWeakSquares     * popcount(weak & ei->kingAreas[US])
                + SafetyNoEnemyQueens   * !enemyQueens
                + SafetySafeQueenCheck  * popcount(queenChecks)
                + SafetySafeRookCheck   * popcount(rookChecks)
                + SafetySafeBishopCheck * popcount(bishopChecks)
                + SafetySafeKnightCheck * popcount(knightChecks)
                + ei->pksafety[US]
                + SafetyAdjustment;

        if (TRACE) T.SafetyAttackValue[US]     = scaledAttackCounts;
        if (TRACE) T.SafetyWeakSquares[US]     = popcount(weak & ei->kingAreas[US]);
        if (TRACE) T.SafetyNoEnemyQueens[US]   = !enemyQueens;
        if (TRACE) T.SafetySafeQueenCheck[US]  = popcount(queenChecks);
        if (TRACE) T.SafetySafeRookCheck[US]   = popcount(rookChecks);
        if (TRACE) T.SafetySafeBishopCheck[US] = popcount(bishopChecks);
        if (TRACE) T.SafetySafeKnightCheck[US] = popcount(knightChecks);
        if (TRACE) T.SafetyAdjustment[US]      = 1;

        // Convert safety to an MG and EG score
        mg = ScoreMG(safety), eg = ScoreEG(safety);
        eval += MakeScore(-mg * MAX(0, mg) / 720, -MAX(0, eg) / 20);
        if (TRACE) T.safety[US] = safety;
    }

    else if (TRACE) {
        T.SafetyKnightWeight[US] = 0;
        T.SafetyBishopWeight[US] = 0;
        T.SafetyRookWeight[US]   = 0;
        T.SafetyQueenWeight[US]  = 0;

        for (int i=0;i<8;i++) {
            T.SafetyShelter[0][i][US]  = 0;
            T.SafetyShelter[1][i][US]  = 0;
            T.SafetyStorm[0][i][US]    = 0;
            T.SafetyStorm[1][i][US]    = 0;
        }
    }

    return eval;
}

int evaluatePassed(EvalInfo *ei, Board *board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, rank, dist, canAdvance, safeAdvance, eval = 0;

    uint64_t bitboard;
    uint64_t myPassers = board->colours[US] & ei->passedPawns;
    uint64_t occupied  = board->colours[WHITE] | board->colours[BLACK];
    uint64_t tempPawns = myPassers;

    // Evaluate each passed pawn
    while (tempPawns) {

        // Pop off the next passed Pawn
        sq = poplsb(&tempPawns);
        rank = relativeRankOf(US, sq);
        bitboard = pawnAdvance(1ull << sq, 0ull, US);

        // Evaluate based on rank, ability to advance, and safety
        canAdvance = !(bitboard & occupied);
        safeAdvance = !(bitboard & ei->attacked[THEM]);
        eval += PassedPawn[canAdvance][safeAdvance][rank];
        if (TRACE) T.PassedPawn[canAdvance][safeAdvance][rank][US]++;

        // Short-circuit evaluation for additional passers on a file
        if (several(forwardFileMasks(US, sq) & myPassers)) continue;

        // Evaluate based on distance from our king
        dist = distanceBetween(sq, ei->kingSquare[US]);
        eval += dist * PassedFriendlyDistance[rank];
        if (TRACE) T.PassedFriendlyDistance[rank][US] += dist;

        // Evaluate based on distance from their king
        dist = distanceBetween(sq, ei->kingSquare[THEM]);
        eval += dist * PassedEnemyDistance[rank];
        if (TRACE) T.PassedEnemyDistance[rank][US] += dist;

        // Apply a bonus when the path to promoting is uncontested
        // bitboard = forwardRanksMasks(US, rankOf(sq)) & Files[fileOf(sq)];
        // flag = !(bitboard & (board->colours[THEM] | ei->attacked[THEM]));
        // eval += flag * PassedSafePromotionPath;
        // if (TRACE) T.PassedSafePromotionPath[US] += flag;
    }

    return eval;
}

int evaluateThreats(EvalInfo *ei, Board *board, int colour) {

    const int US = colour, THEM = !colour;
    // const uint64_t Rank3Rel = US == WHITE ? RANK_3 : RANK_6;

    int count, eval = 0;

    uint64_t friendly = board->colours[  US];
    // uint64_t enemy    = board->colours[THEM];
    // uint64_t occupied = friendly | enemy;

    uint64_t pawns   = friendly & board->pieces[PAWN  ];
    uint64_t knights = friendly & board->pieces[KNIGHT];
    uint64_t bishops = friendly & board->pieces[BISHOP];
    uint64_t rooks   = friendly & board->pieces[ROOK  ];
    uint64_t queens  = friendly & board->pieces[QUEEN ];

    uint64_t attacksByPawns  = ei->attackedBy[THEM][PAWN  ];
    uint64_t attacksByMinors = ei->attackedBy[THEM][KNIGHT] | ei->attackedBy[THEM][BISHOP];
    // uint64_t attacksByMajors = ei->attackedBy[THEM][ROOK  ] | ei->attackedBy[THEM][QUEEN ];

    // Squares with more attackers, few defenders, and no pawn support
    uint64_t poorlyDefended = (ei->attacked[THEM] & ~ei->attacked[US])
                            | (ei->attackedBy2[THEM] & ~ei->attackedBy2[US] & ~ei->attackedBy[US][PAWN]);

    // uint64_t weakMinors = (knights | bishops) & poorlyDefended;

    // A friendly minor or major is overloaded if attacked and defended by exactly one
    // uint64_t overloaded = (knights | bishops | rooks | queens)
    //                     & ei->attacked[  US] & ~ei->attackedBy2[  US]
    //                     & ei->attacked[THEM] & ~ei->attackedBy2[THEM];

    // Look for enemy non-pawn pieces which we may threaten with a pawn advance.
    // Don't consider pieces we already threaten, pawn moves which would be countered
    // by a pawn capture, and squares which are completely unprotected by our pieces.
    // uint64_t pushThreat  = pawnAdvance(pawns, occupied, US);
    // pushThreat |= pawnAdvance(pushThreat & ~attacksByPawns & Rank3Rel, occupied, US);
    // pushThreat &= ~attacksByPawns & (ei->attacked[US] | ~ei->attacked[THEM]);
    // pushThreat  = pawnAttackSpan(pushThreat, enemy & ~ei->attackedBy[US][PAWN], US);

    // Penalty for each of our poorly supported pawns
    count = popcount(pawns & ~attacksByPawns & poorlyDefended);
    eval += count * ThreatWeakPawn;
    if (TRACE) T.ThreatWeakPawn[US] += count;

    // Penalty for pawn threats against our minors
    count = popcount((knights | bishops) & attacksByPawns);
    eval += count * ThreatMinorAttackedByPawn;
    if (TRACE) T.ThreatMinorAttackedByPawn[US] += count;

    // Penalty for any minor threat against minor pieces
    // count = popcount((knights | bishops) & attacksByMinors);
    // eval += count * ThreatMinorAttackedByMinor;
    // if (TRACE) T.ThreatMinorAttackedByMinor[US] += count;

    // Penalty for all major threats against poorly supported minors
    // count = popcount(weakMinors & attacksByMajors);
    // eval += count * ThreatMinorAttackedByMajor;
    // if (TRACE) T.ThreatMinorAttackedByMajor[US] += count;

    // Penalty for pawn and minor threats against our rooks
    count = popcount(rooks & (attacksByPawns | attacksByMinors));
    eval += count * ThreatRookAttackedByLesser;
    if (TRACE) T.ThreatRookAttackedByLesser[US] += count;

    // Penalty for king threats against our poorly defended minors
    // count = popcount(weakMinors & ei->attackedBy[THEM][KING]);
    // eval += count * ThreatMinorAttackedByKing;
    // if (TRACE) T.ThreatMinorAttackedByKing[US] += count;

    // Penalty for king threats against our poorly defended rooks
    // count = popcount(rooks & poorlyDefended & ei->attackedBy[THEM][KING]);
    // eval += count * ThreatRookAttackedByKing;
    // if (TRACE) T.ThreatRookAttackedByKing[US] += count;

    // Penalty for any threat against our queens
    count = popcount(queens & ei->attacked[THEM]);
    eval += count * ThreatQueenAttackedByOne;
    if (TRACE) T.ThreatQueenAttackedByOne[US] += count;

    // Penalty for any overloaded minors or majors
    // count = popcount(overloaded);
    // eval += count * ThreatOverloadedPieces;
    // if (TRACE) T.ThreatOverloadedPieces[US] += count;

    // Bonus for giving threats by safe pawn pushes
    // count = popcount(pushThreat);
    // eval += count * ThreatByPawnPush;
    // if (TRACE) T.ThreatByPawnPush[colour] += count;

    return eval;
}

int evaluateSpace(EvalInfo *ei, Board *board, int colour) {

    const int US = colour, THEM = !colour;

    int count, eval = 0;

    uint64_t friendly = board->colours[  US];
    uint64_t enemy    = board->colours[THEM];

    // Squares we attack with more enemy attackers and no friendly pawn attacks
    uint64_t uncontrolled =   ei->attackedBy2[THEM] & ei->attacked[US]
                           & ~ei->attackedBy2[US  ] & ~ei->attackedBy[US][PAWN];

    // Penalty for restricted piece moves
    count = popcount(uncontrolled & (friendly | enemy));
    eval += count * SpaceRestrictPiece;
    if (TRACE) T.SpaceRestrictPiece[US] += count;

    count = popcount(uncontrolled & ~friendly & ~enemy);
    eval += count * SpaceRestrictEmpty;
    if (TRACE) T.SpaceRestrictEmpty[US] += count;

    // Bonus for uncontested central squares
    // This is mostly relevant in the opening and the early middlegame, while rarely correct
    // in the endgame where one rook or queen could control many uncontested squares.
    // Thus we don't apply this term when below a threshold of minors/majors count.
    if (      popcount(board->pieces[KNIGHT] | board->pieces[BISHOP])
        + 2 * popcount(board->pieces[ROOK  ] | board->pieces[QUEEN ]) > 12) {
        count = popcount(~ei->attacked[THEM] & (ei->attacked[US] | friendly) & CENTER_BIG);
        eval += count * SpaceCenterControl;
        if (TRACE) T.SpaceCenterControl[US] += count;
    }

    return eval;
}

int evaluateClosedness(EvalInfo *ei, Board *board) {

    int closedness, count, eval = 0;

    uint64_t white = board->colours[WHITE];
    uint64_t black = board->colours[BLACK];

    uint64_t knights = board->pieces[KNIGHT];
    uint64_t rooks   = board->pieces[ROOK  ];

    // Compute Closedness factor for this position
    closedness = 1 * popcount(board->pieces[PAWN])
               + 3 * popcount(ei->rammedPawns[WHITE])
               - 4 * openFileCount(board->pieces[PAWN]);
    closedness = MAX(0, MIN(8, closedness / 3));

    // Evaluate Knights based on how Closed the position is
    count = popcount(white & knights) - popcount(black & knights);
    eval += count * ClosednessKnightAdjustment[closedness];
    if (TRACE) T.ClosednessKnightAdjustment[closedness][WHITE] += count;

    // Evaluate Rooks based on how Closed the position is
    count = popcount(white & rooks) - popcount(black & rooks);
    eval += count * ClosednessRookAdjustment[closedness];
    if (TRACE) T.ClosednessRookAdjustment[closedness][WHITE] += count;

    return eval;
}

int evaluateComplexity(EvalInfo *ei, Board *board, int eval) {

    // Adjust endgame evaluation based on features related to how
    // likely the stronger side is to convert the position.
    // More often than not, this is a penalty for drawish positions.

    (void) ei; // Silence compiler warning

    int complexity;
    int eg = ScoreEG(eval);
    int sign = (eg > 0) - (eg < 0);

    int pawnsOnBothFlanks = (board->pieces[PAWN] & LEFT_FLANK )
                         && (board->pieces[PAWN] & RIGHT_FLANK);

    uint64_t knights = board->pieces[KNIGHT];
    uint64_t bishops = board->pieces[BISHOP];
    uint64_t rooks   = board->pieces[ROOK  ];
    uint64_t queens  = board->pieces[QUEEN ];

    // Compute the initiative bonus or malus for the attacking side
    complexity =  ComplexityTotalPawns  * popcount(board->pieces[PAWN])
               +  ComplexityPawnFlanks  * pawnsOnBothFlanks
               +  ComplexityPawnEndgame * !(knights | bishops | rooks | queens)
               +  ComplexityAdjustment;

    if (TRACE) T.ComplexityTotalPawns[WHITE]  += popcount(board->pieces[PAWN]);
    if (TRACE) T.ComplexityPawnFlanks[WHITE]  += pawnsOnBothFlanks;
    if (TRACE) T.ComplexityPawnEndgame[WHITE] += !(knights | bishops | rooks | queens);
    if (TRACE) T.ComplexityAdjustment[WHITE]  += 1;

    // Avoid changing which side has the advantage
    int v = sign * MAX(ScoreEG(complexity), -abs(eg));

    if (TRACE) T.eval       = eval;
    if (TRACE) T.complexity = complexity;
    return MakeScore(0, v);
}

int evaluateScaleFactor(Board *board, int eval) {

    // Scale endgames based upon the remaining material. We check
    // for various Opposite Coloured Bishop cases, positions with
    // a lone Queen against multiple minor pieces and/or rooks, and
    // positions with a Lone minor that should not be winnable

    const uint64_t pawns   = board->pieces[PAWN  ];
    const uint64_t knights = board->pieces[KNIGHT];
    const uint64_t bishops = board->pieces[BISHOP];
    const uint64_t rooks   = board->pieces[ROOK  ];
    const uint64_t queens  = board->pieces[QUEEN ];

    const uint64_t minors  = knights | bishops;
    const uint64_t pieces  = knights | bishops | rooks;

    const uint64_t white   = board->colours[WHITE];
    const uint64_t black   = board->colours[BLACK];

    const uint64_t weak    = ScoreEG(eval) < 0 ? white : black;
    const uint64_t strong  = ScoreEG(eval) < 0 ? black : white;


    // Check for opposite coloured bishops
    if (   onlyOne(white & bishops)
        && onlyOne(black & bishops)
        && onlyOne(bishops & WHITE_SQUARES)) {

        // Scale factor for OCB + knights
        if ( !(rooks | queens)
            && onlyOne(white & knights)
            && onlyOne(black & knights))
            return SCALE_OCB_ONE_KNIGHT;

        // Scale factor for OCB + rooks
        if ( !(knights | queens)
            && onlyOne(white & rooks)
            && onlyOne(black & rooks))
            return SCALE_OCB_ONE_ROOK;

        // Scale factor for lone OCB
        if (!(knights | rooks | queens))
            return SCALE_OCB_BISHOPS_ONLY;
    }

    // Lone Queens are weak against multiple pieces
    if (onlyOne(queens) && several(pieces) && pieces == (weak & pieces))
        return SCALE_LONE_QUEEN;

    // Lone Minor vs King + Pawns should never be won
    if ((strong & minors) && popcount(strong) == 2)
        return SCALE_DRAW;

    // Scale up lone pieces with massive pawn advantages
    if (   !queens
        && !several(pieces & white)
        && !several(pieces & black)
        &&  popcount(strong & pawns) - popcount(weak & pawns) > 2)
        return SCALE_LARGE_PAWN_ADV;

    return SCALE_NORMAL;
}

void initEvalInfo(Thread *thread, Board *board, EvalInfo *ei) {

    uint64_t white   = board->colours[WHITE];
    uint64_t black   = board->colours[BLACK];

    uint64_t pawns   = board->pieces[PAWN  ];
    uint64_t bishops = board->pieces[BISHOP] | board->pieces[QUEEN];
    uint64_t rooks   = board->pieces[ROOK  ] | board->pieces[QUEEN];
    uint64_t kings   = board->pieces[KING  ];

    // Save some general information about the pawn structure for later
    ei->pawnAttacks[WHITE]    = pawnAttackSpan(white & pawns, ~0ull, WHITE);
    ei->pawnAttacks[BLACK]    = pawnAttackSpan(black & pawns, ~0ull, BLACK);
    ei->pawnAttacksBy2[WHITE] = pawnAttackDouble(white & pawns, ~0ull, WHITE);
    ei->pawnAttacksBy2[BLACK] = pawnAttackDouble(black & pawns, ~0ull, BLACK);
    ei->rammedPawns[WHITE]    = pawnAdvance(black & pawns, ~(white & pawns), BLACK);
    ei->rammedPawns[BLACK]    = pawnAdvance(white & pawns, ~(black & pawns), WHITE);
    ei->blockedPawns[WHITE]   = pawnAdvance(white | black, ~(white & pawns), BLACK);
    ei->blockedPawns[BLACK]   = pawnAdvance(white | black, ~(black & pawns), WHITE);

    // Compute an area for evaluating our King's safety.
    // The definition of the King Area can be found in masks.c
    ei->kingSquare[WHITE] = getlsb(white & kings);
    ei->kingSquare[BLACK] = getlsb(black & kings);
    ei->kingAreas[WHITE] = kingAreaMasks(WHITE, ei->kingSquare[WHITE]);
    ei->kingAreas[BLACK] = kingAreaMasks(BLACK, ei->kingSquare[BLACK]);

    // Exclude squares attacked by our opponents, our blocked pawns, and our own King
    ei->mobilityAreas[WHITE] = ~(ei->pawnAttacks[BLACK] | (white & kings) | ei->blockedPawns[WHITE]);
    ei->mobilityAreas[BLACK] = ~(ei->pawnAttacks[WHITE] | (black & kings) | ei->blockedPawns[BLACK]);

    // Init part of the attack tables. By doing this step here, evaluatePawns()
    // can start by setting up the attackedBy2 table, since King attacks are resolved
    ei->attacked[WHITE] = ei->attackedBy[WHITE][KING] = kingAttacks(ei->kingSquare[WHITE]);
    ei->attacked[BLACK] = ei->attackedBy[BLACK][KING] = kingAttacks(ei->kingSquare[BLACK]);

    // For mobility, we allow bishops to attack through each other
    ei->occupiedMinusBishops[WHITE] = (white | black) ^ (white & bishops);
    ei->occupiedMinusBishops[BLACK] = (white | black) ^ (black & bishops);

    // For mobility, we allow rooks to attack through each other
    ei->occupiedMinusRooks[WHITE] = (white | black) ^ (white & rooks);
    ei->occupiedMinusRooks[BLACK] = (white | black) ^ (black & rooks);

    // Init all of the King Safety information
    ei->kingAttacksCount[WHITE]    = ei->kingAttacksCount[BLACK]    = 0;
    ei->kingAttackersCount[WHITE]  = ei->kingAttackersCount[BLACK]  = 0;
    ei->kingAttackersWeight[WHITE] = ei->kingAttackersWeight[BLACK] = 0;

    // Try to read a hashed Pawn King Eval. Otherwise, start from scratch
    ei->pkentry         = getCachedPawnKingEval(thread, board);
    ei->passedPawns     = ei->pkentry == NULL ? 0ull : ei->pkentry->passed;
    ei->pkeval[WHITE]   = ei->pkentry == NULL ? 0    : ei->pkentry->eval;
    ei->pkeval[BLACK]   = ei->pkentry == NULL ? 0    : 0;
    ei->pksafety[WHITE] = ei->pkentry == NULL ? 0    : ei->pkentry->safetyw;
    ei->pksafety[BLACK] = ei->pkentry == NULL ? 0    : ei->pkentry->safetyb;
}

void initEval() {

    // Init a normalized 64-length PSQT for the evaluation which
    // combines the Piece Values with the original PSQT Values

    for (int sq = 0; sq < SQUARE_NB; sq++) {

        const int sq1 = relativeSquare(WHITE, sq);
        const int sq2 = relativeSquare(BLACK, sq);

        PSQT[WHITE_PAWN  ][sq] = + PawnValue   +   PawnPSQT[sq1];
        PSQT[WHITE_KNIGHT][sq] = + KnightValue + KnightPSQT[sq1];
        PSQT[WHITE_BISHOP][sq] = + BishopValue + BishopPSQT[sq1];
        PSQT[WHITE_ROOK  ][sq] = + RookValue   +   RookPSQT[sq1];
        PSQT[WHITE_QUEEN ][sq] = + QueenValue  +  QueenPSQT[sq1];
        PSQT[WHITE_KING  ][sq] = + KingValue   +   KingPSQT[sq1];

        PSQT[BLACK_PAWN  ][sq] = - PawnValue   -   PawnPSQT[sq2];
        PSQT[BLACK_KNIGHT][sq] = - KnightValue - KnightPSQT[sq2];
        PSQT[BLACK_BISHOP][sq] = - BishopValue - BishopPSQT[sq2];
        PSQT[BLACK_ROOK  ][sq] = - RookValue   -   RookPSQT[sq2];
        PSQT[BLACK_QUEEN ][sq] = - QueenValue  -  QueenPSQT[sq2];
        PSQT[BLACK_KING  ][sq] = - KingValue   -   KingPSQT[sq2];
    }
}
