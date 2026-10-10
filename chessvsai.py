#!/usr/bin/env python3
"""
Chess vs AI  -  single-file pygame chess game.

Features
  * Full rules: castling, en passant, promotion (with picker), check,
    checkmate, stalemate, 50-move rule, threefold repetition,
    insufficient material
  * AI opponent: negamax + alpha-beta, iterative deepening with a time limit,
    quiescence search, piece-square tables, move ordering, small opening book
  * 3 difficulty levels, play as White or Black, undo, flip board
  * AI thinks in a background thread so the window never freezes


Controls
  Click a piece, then click a highlighted square to move.
  N = new game   U = undo   F = flip board   Esc = quit
"""

import sys
import time
import random
import threading

import pygame

# --------------------------------------------------------------------------
#  Engine
# --------------------------------------------------------------------------

FILES = "abcdefgh"
WK, WQ, BK, BQ = 1, 2, 4, 8
CMASK = {
    (7, 4): WK | WQ, (7, 7): WK, (7, 0): WQ,
    (0, 4): BK | BQ, (0, 7): BK, (0, 0): BQ,
}

KNIGHT_D = [(-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)]
KING_D = [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]
ROOK_D = [(-1, 0), (1, 0), (0, -1), (0, 1)]
BISHOP_D = [(-1, -1), (-1, 1), (1, -1), (1, 1)]

VAL = {'P': 100, 'N': 320, 'B': 330, 'R': 500, 'Q': 900, 'K': 0}
MATE = 100000
INF = 10 ** 9

# Piece-square tables (white's point of view, row 0 = rank 8)
PAWN_T = [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [50, 50, 50, 50, 50, 50, 50, 50],
    [10, 10, 20, 30, 30, 20, 10, 10],
    [5, 5, 10, 25, 25, 10, 5, 5],
    [0, 0, 0, 20, 20, 0, 0, 0],
    [5, -5, -10, 0, 0, -10, -5, 5],
    [5, 10, 10, -20, -20, 10, 10, 5],
    [0, 0, 0, 0, 0, 0, 0, 0]]
KNIGHT_T = [
    [-50, -40, -30, -30, -30, -30, -40, -50],
    [-40, -20, 0, 0, 0, 0, -20, -40],
    [-30, 0, 10, 15, 15, 10, 0, -30],
    [-30, 5, 15, 20, 20, 15, 5, -30],
    [-30, 0, 15, 20, 20, 15, 0, -30],
    [-30, 5, 10, 15, 15, 10, 5, -30],
    [-40, -20, 0, 5, 5, 0, -20, -40],
    [-50, -40, -30, -30, -30, -30, -40, -50]]
BISHOP_T = [
    [-20, -10, -10, -10, -10, -10, -10, -20],
    [-10, 0, 0, 0, 0, 0, 0, -10],
    [-10, 0, 5, 10, 10, 5, 0, -10],
    [-10, 5, 5, 10, 10, 5, 5, -10],
    [-10, 0, 10, 10, 10, 10, 0, -10],
    [-10, 10, 10, 10, 10, 10, 10, -10],
    [-10, 5, 0, 0, 0, 0, 5, -10],
    [-20, -10, -10, -10, -10, -10, -10, -20]]
ROOK_T = [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [5, 10, 10, 10, 10, 10, 10, 5],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [0, 0, 0, 5, 5, 0, 0, 0]]
QUEEN_T = [
    [-20, -10, -10, -5, -5, -10, -10, -20],
    [-10, 0, 0, 0, 0, 0, 0, -10],
    [-10, 0, 5, 5, 5, 5, 0, -10],
    [-5, 0, 5, 5, 5, 5, 0, -5],
    [0, 0, 5, 5, 5, 5, 0, -5],
    [-10, 5, 5, 5, 5, 5, 0, -10],
    [-10, 0, 5, 0, 0, 0, 0, -10],
    [-20, -10, -10, -5, -5, -10, -10, -20]]
KING_MID_T = [
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-20, -30, -30, -40, -40, -30, -30, -20],
    [-10, -20, -20, -20, -20, -20, -20, -10],
    [20, 20, 0, 0, 0, 0, 20, 20],
    [20, 30, 10, 0, 0, 10, 30, 20]]
KING_END_T = [
    [-50, -40, -30, -20, -20, -30, -40, -50],
    [-30, -20, -10, 0, 0, -10, -20, -30],
    [-30, -10, 20, 30, 30, 20, -10, -30],
    [-30, -10, 30, 40, 40, 30, -10, -30],
    [-30, -10, 30, 40, 40, 30, -10, -30],
    [-30, -10, 20, 30, 30, 20, -10, -30],
    [-30, -30, 0, 0, 0, 0, -30, -30],
    [-50, -30, -30, -30, -30, -30, -30, -50]]
PST = {'P': PAWN_T, 'N': KNIGHT_T, 'B': BISHOP_T, 'R': ROOK_T, 'Q': QUEEN_T}


def opp(color):
    return 'b' if color == 'w' else 'w'


def coord(m):
    return f"{FILES[m[1]]}{8 - m[0]}{FILES[m[3]]}{8 - m[2]}"


def sq_name(r, c):
    return f"{FILES[c]}{8 - r}"


def initial_board():
    back = ['R', 'N', 'B', 'Q', 'K', 'B', 'N', 'R']
    board = [['b' + p for p in back]]
    board.append(['bP'] * 8)
    for _ in range(4):
        board.append(['.'] * 8)
    board.append(['wP'] * 8)
    board.append(['w' + p for p in back])
    return board


class Position:
    """Board state with make / unmake. Move = (from_r, from_c, to_r, to_c, promo)."""

    def __init__(self):
        self.board = initial_board()
        self.turn = 'w'
        self.rights = WK | WQ | BK | BQ
        self.ep = None
        self.halfmove = 0
        self.fullmove = 1
        self.king = {'w': (7, 4), 'b': (0, 4)}
        self.stack = []

    def copy(self):
        p = Position.__new__(Position)
        p.board = [row[:] for row in self.board]
        p.turn = self.turn
        p.rights = self.rights
        p.ep = self.ep
        p.halfmove = self.halfmove
        p.fullmove = self.fullmove
        p.king = dict(self.king)
        p.stack = []
        return p

    def key(self):
        return (tuple(tuple(r) for r in self.board), self.turn, self.rights, self.ep)

    # ---- attack detection ------------------------------------------------
    def attacked(self, r, c, by):
        b = self.board
        pr = r + 1 if by == 'w' else r - 1
        if 0 <= pr < 8:
            target = by + 'P'
            if c > 0 and b[pr][c - 1] == target:
                return True
            if c < 7 and b[pr][c + 1] == target:
                return True
        target = by + 'N'
        for dr, dc in KNIGHT_D:
            rr, cc = r + dr, c + dc
            if 0 <= rr < 8 and 0 <= cc < 8 and b[rr][cc] == target:
                return True
        target = by + 'K'
        for dr, dc in KING_D:
            rr, cc = r + dr, c + dc
            if 0 <= rr < 8 and 0 <= cc < 8 and b[rr][cc] == target:
                return True
        t1, t2 = by + 'R', by + 'Q'
        for dr, dc in ROOK_D:
            rr, cc = r + dr, c + dc
            while 0 <= rr < 8 and 0 <= cc < 8:
                p = b[rr][cc]
                if p != '.':
                    if p == t1 or p == t2:
                        return True
                    break
                rr += dr
                cc += dc
        t1 = by + 'B'
        for dr, dc in BISHOP_D:
            rr, cc = r + dr, c + dc
            while 0 <= rr < 8 and 0 <= cc < 8:
                p = b[rr][cc]
                if p != '.':
                    if p == t1 or p == t2:
                        return True
                    break
                rr += dr
                cc += dc
        return False

    def in_check(self, color):
        kr, kc = self.king[color]
        return self.attacked(kr, kc, opp(color))

    # ---- move generation -------------------------------------------------
    def pseudo_moves(self, captures_only=False):
        moves = []
        b = self.board
        us = self.turn
        them = opp(us)
        for r in range(8):
            row = b[r]
            for c in range(8):
                p = row[c]
                if p == '.' or p[0] != us:
                    continue
                t = p[1]
                if t == 'P':
                    d = -1 if us == 'w' else 1
                    start = 6 if us == 'w' else 1
                    last = 0 if us == 'w' else 7
                    nr = r + d
                    if not (0 <= nr < 8):
                        continue
                    if b[nr][c] == '.':
                        if nr == last:
                            if captures_only:
                                moves.append((r, c, nr, c, 'Q'))
                            else:
                                for pr in 'QRBN':
                                    moves.append((r, c, nr, c, pr))
                        elif not captures_only:
                            moves.append((r, c, nr, c, None))
                            if r == start and b[nr + d][c] == '.':
                                moves.append((r, c, nr + d, c, None))
                    for dc in (-1, 1):
                        nc = c + dc
                        if 0 <= nc < 8:
                            tp = b[nr][nc]
                            if tp != '.' and tp[0] == them:
                                if nr == last:
                                    for pr in 'QRBN':
                                        moves.append((r, c, nr, nc, pr))
                                else:
                                    moves.append((r, c, nr, nc, None))
                            elif tp == '.' and (nr, nc) == self.ep:
                                moves.append((r, c, nr, nc, None))
                elif t == 'N' or t == 'K':
                    for dr, dc in (KNIGHT_D if t == 'N' else KING_D):
                        rr, cc = r + dr, c + dc
                        if 0 <= rr < 8 and 0 <= cc < 8:
                            tp = b[rr][cc]
                            if tp == '.':
                                if not captures_only:
                                    moves.append((r, c, rr, cc, None))
                            elif tp[0] == them:
                                moves.append((r, c, rr, cc, None))
                    if t == 'K' and not captures_only:
                        self._castle_moves(moves, r, c, us, them)
                else:
                    dirs = ROOK_D if t == 'R' else BISHOP_D if t == 'B' else ROOK_D + BISHOP_D
                    for dr, dc in dirs:
                        rr, cc = r + dr, c + dc
                        while 0 <= rr < 8 and 0 <= cc < 8:
                            tp = b[rr][cc]
                            if tp == '.':
                                if not captures_only:
                                    moves.append((r, c, rr, cc, None))
                            else:
                                if tp[0] == them:
                                    moves.append((r, c, rr, cc, None))
                                break
                            rr += dr
                            cc += dc
        return moves

    def _castle_moves(self, moves, r, c, us, them):
        home = 7 if us == 'w' else 0
        if (r, c) != (home, 4):
            return
        kbit, qbit = (WK, WQ) if us == 'w' else (BK, BQ)
        b = self.board
        if not (self.rights & (kbit | qbit)):
            return
        if self.attacked(home, 4, them):
            return
        if (self.rights & kbit and b[home][5] == '.' and b[home][6] == '.'
                and b[home][7] == us + 'R'
                and not self.attacked(home, 5, them)
                and not self.attacked(home, 6, them)):
            moves.append((home, 4, home, 6, None))
        if (self.rights & qbit and b[home][3] == '.' and b[home][2] == '.'
                and b[home][1] == '.' and b[home][0] == us + 'R'
                and not self.attacked(home, 3, them)
                and not self.attacked(home, 2, them)):
            moves.append((home, 4, home, 2, None))

    def legal_moves(self):
        res = []
        us = self.turn
        for m in self.pseudo_moves():
            self.make(m)
            kr, kc = self.king[us]
            if not self.attacked(kr, kc, self.turn):
                res.append(m)
            self.unmake()
        return res

    # ---- make / unmake ---------------------------------------------------
    def make(self, m):
        fr, fc, tr, tc, promo = m
        b = self.board
        p = b[fr][fc]
        us = p[0]
        cap = b[tr][tc]
        cap_pos = (tr, tc)
        if p[1] == 'P' and fc != tc and cap == '.':      # en passant
            cap_pos = (fr, tc)
            cap = b[fr][tc]
            b[fr][tc] = '.'
        self.stack.append((m, p, cap, cap_pos, self.rights, self.ep, self.halfmove))
        b[fr][fc] = '.'
        b[tr][tc] = (us + promo) if promo else p
        if p[1] == 'K':
            self.king[us] = (tr, tc)
            if abs(tc - fc) == 2:
                if tc == 6:
                    b[tr][5] = b[tr][7]
                    b[tr][7] = '.'
                else:
                    b[tr][3] = b[tr][0]
                    b[tr][0] = '.'
        self.rights &= ~(CMASK.get((fr, fc), 0) | CMASK.get((tr, tc), 0))
        self.ep = ((fr + tr) // 2, fc) if (p[1] == 'P' and abs(tr - fr) == 2) else None
        self.halfmove = 0 if (p[1] == 'P' or cap != '.') else self.halfmove + 1
        if us == 'b':
            self.fullmove += 1
        self.turn = opp(us)

    def unmake(self):
        m, p, cap, cap_pos, rights, ep, hm = self.stack.pop()
        fr, fc, tr, tc, promo = m
        b = self.board
        us = p[0]
        self.turn = us
        b[fr][fc] = p
        b[tr][tc] = '.'
        if cap != '.':
            b[cap_pos[0]][cap_pos[1]] = cap
        if p[1] == 'K':
            self.king[us] = (fr, fc)
            if abs(tc - fc) == 2:
                if tc == 6:
                    b[tr][7] = b[tr][5]
                    b[tr][5] = '.'
                else:
                    b[tr][0] = b[tr][3]
                    b[tr][3] = '.'
        self.rights = rights
        self.ep = ep
        self.halfmove = hm
        if us == 'b':
            self.fullmove -= 1


def insufficient_material(pos):
    pcs = [p for row in pos.board for p in row if p != '.' and p[1] != 'K']
    if not pcs:
        return True
    return len(pcs) == 1 and pcs[0][1] in 'BN'


def to_san(pos, m, legal):
    """Standard algebraic notation for move m (must be called before making it)."""
    fr, fc, tr, tc, pr = m
    p = pos.board[fr][fc]
    t = p[1]
    if t == 'K' and abs(tc - fc) == 2:
        s = 'O-O' if tc == 6 else 'O-O-O'
    else:
        capture = pos.board[tr][tc] != '.' or (t == 'P' and fc != tc)
        s = ''
        if t == 'P':
            if capture:
                s += FILES[fc] + 'x'
        else:
            s += t
            others = [o for o in legal if o != m and pos.board[o[0]][o[1]] == p
                      and (o[2], o[3]) == (tr, tc)]
            if others:
                if all(o[1] != fc for o in others):
                    s += FILES[fc]
                elif all(o[0] != fr for o in others):
                    s += str(8 - fr)
                else:
                    s += FILES[fc] + str(8 - fr)
            if capture:
                s += 'x'
        s += sq_name(tr, tc)
        if pr:
            s += '=' + pr
    pos.make(m)
    if pos.in_check(pos.turn):
        s += '#' if not pos.legal_moves() else '+'
    pos.unmake()
    return s


# --------------------------------------------------------------------------
#  Evaluation & search
# --------------------------------------------------------------------------

def evaluate(pos):
    """Static evaluation in centipawns from the side-to-move's perspective."""
    b = pos.board
    score = 0
    non_pawn = 0
    for r in range(8):
        row = b[r]
        for c in range(8):
            p = row[c]
            if p == '.':
                continue
            t = p[1]
            if t == 'K':
                continue
            v = VAL[t]
            if t != 'P':
                non_pawn += v
            if p[0] == 'w':
                score += v + PST[t][r][c]
            else:
                score -= v + PST[t][7 - r][c]
    table = KING_END_T if non_pawn <= 2600 else KING_MID_T
    wr, wc = pos.king['w']
    br, bc = pos.king['b']
    score += table[wr][wc]
    score -= table[7 - br][bc]
    return score if pos.turn == 'w' else -score


class SearchAbort(Exception):
    pass


class Searcher:
    def __init__(self, pos, max_depth, time_limit, noise, stop_event):
        self.pos = pos
        self.max_depth = max_depth
        self.deadline = time.time() + time_limit
        self.noise = noise
        self.stop = stop_event
        self.nodes = 0

    def _check(self):
        if self.stop.is_set() or time.time() > self.deadline:
            raise SearchAbort()

    def order_key(self, m):
        b = self.pos.board
        v = b[m[2]][m[3]]
        s = 0
        if v != '.':
            s = 1000 + 10 * VAL[v[1]] - VAL[b[m[0]][m[1]][1]]
        if m[4]:
            s += VAL[m[4]]
        return -s

    def best_move(self):
        pos = self.pos
        legal = pos.legal_moves()
        if not legal:
            return None
        if len(legal) == 1:
            return legal[0]
        legal.sort(key=self.order_key)
        best = legal[0]
        for depth in range(1, self.max_depth + 1):
            try:
                alpha, beta = -INF, INF
                it_best, it_score = None, -INF
                for m in legal:
                    pos.make(m)
                    s = -self._negamax(depth - 1, -beta, -alpha, 1)
                    pos.unmake()
                    if self.noise:
                        s += random.uniform(-self.noise, self.noise)
                    if s > it_score:
                        it_score, it_best = s, m
                    if not self.noise and s > alpha:
                        alpha = s
            except SearchAbort:
                break
            best = it_best
            legal.remove(best)
            legal.insert(0, best)
            if it_score > MATE - 100:
                break
        return best

    def _negamax(self, depth, alpha, beta, ply):
        self.nodes += 1
        if self.nodes & 511 == 0:
            self._check()
        pos = self.pos
        if pos.halfmove >= 100:
            return 0
        us = pos.turn
        in_check = pos.in_check(us)
        if in_check and ply < 12:
            depth += 1
        if depth <= 0:
            return self._quiesce(alpha, beta, 0)
        best = -INF
        legal_count = 0
        for m in sorted(pos.pseudo_moves(), key=self.order_key):
            pos.make(m)
            kr, kc = pos.king[us]
            if pos.attacked(kr, kc, pos.turn):
                pos.unmake()
                continue
            legal_count += 1
            score = -self._negamax(depth - 1, -beta, -alpha, ply + 1)
            pos.unmake()
            if score > best:
                best = score
            if best > alpha:
                alpha = best
            if alpha >= beta:
                break
        if legal_count == 0:
            return (-MATE + ply) if in_check else 0
        return best

    def _quiesce(self, alpha, beta, qd):
        self.nodes += 1
        if self.nodes & 511 == 0:
            self._check()
        pos = self.pos
        stand = evaluate(pos)
        if qd >= 8:
            return stand
        if stand >= beta:
            return stand
        if stand > alpha:
            alpha = stand
        us = pos.turn
        for m in sorted(pos.pseudo_moves(captures_only=True), key=self.order_key):
            pos.make(m)
            kr, kc = pos.king[us]
            if pos.attacked(kr, kc, pos.turn):
                pos.unmake()
                continue
            score = -self._quiesce(-beta, -alpha, qd + 1)
            pos.unmake()
            if score >= beta:
                return score
            if score > alpha:
                alpha = score
        return alpha


LEVELS = {
    'Easy':   dict(depth=1, time=1.0, noise=140),
    'Medium': dict(depth=4, time=3.0, noise=0),
    'Hard':   dict(depth=6, time=7.0, noise=0),
}

BOOK_FIRST = ['e2e4', 'd2d4', 'g1f3', 'c2c4']
BOOK_REPLY = {
    'e2e4': ['e7e5', 'c7c5', 'e7e6', 'c7c6'],
    'd2d4': ['d7d5', 'g8f6', 'e7e6'],
    'g1f3': ['d7d5', 'g8f6'],
    'c2c4': ['e7e5', 'g8f6', 'c7c5'],
}

# --------------------------------------------------------------------------
#  GUI
# --------------------------------------------------------------------------

SQ = 80
BOARD = SQ * 8
PANEL = 260
WIN_W, WIN_H = BOARD + PANEL, BOARD
LIGHT = (240, 217, 181)
DARK = (181, 136, 99)
GLYPHS = {'K': '\u265A', 'Q': '\u265B', 'R': '\u265C', 'B': '\u265D', 'N': '\u265E', 'P': '\u265F'}


def find_glyph_font(size):
    names = ['segoeuisymbol', 'dejavusans', 'applesymbols', 'freeserif', 'notosanssymbols2',
             'symbola', 'arialunicodems', 'menlo', 'notosanssymbols', 'freesans']
    for n in names:
        path = pygame.font.match_font(n)
        if not path:
            continue
        try:
            f = pygame.font.Font(path, size)
            m = f.metrics('\u265A\u265F')
            if m and m[0] is not None and m[1] is not None:
                return f
        except Exception:
            continue
    return None


def build_piece_surfaces():
    glyph_font = find_glyph_font(int(SQ * 0.85))
    letter_font = pygame.font.SysFont("arial,helvetica,dejavusans", 40, bold=True)
    surfs = {}
    for col in 'wb':
        for t in 'KQRBNP':
            surf = pygame.Surface((SQ, SQ), pygame.SRCALPHA)
            center = (SQ // 2, SQ // 2)
            if glyph_font:
                fill = (252, 252, 252) if col == 'w' else (22, 22, 22)
                edge = (25, 25, 25) if col == 'w' else (150, 150, 150)
                base = glyph_font.render(GLYPHS[t], True, edge)
                top = glyph_font.render(GLYPHS[t], True, fill)
                for dx, dy in [(-2, 0), (2, 0), (0, -2), (0, 2), (-1, -1), (1, -1), (-1, 1), (1, 1)]:
                    surf.blit(base, base.get_rect(center=(center[0] + dx, center[1] + dy)))
                surf.blit(top, top.get_rect(center=center))
            else:
                fill = (245, 245, 245) if col == 'w' else (40, 40, 40)
                txtc = (30, 30, 30) if col == 'w' else (235, 235, 235)
                pygame.draw.circle(surf, (20, 20, 20), center, 31)
                pygame.draw.circle(surf, fill, center, 29)
                txt = letter_font.render(t, True, txtc)
                surf.blit(txt, txt.get_rect(center=center))
            surfs[col + t] = surf
    return surfs


class Button:
    def __init__(self, rect, label, action, active=None):
        self.rect = pygame.Rect(rect)
        self.label = label
        self.action = action
        self.active = active

    def draw(self, screen, font, mouse):
        on = self.active() if self.active else False
        if on:
            col = (90, 140, 90)
        elif self.rect.collidepoint(mouse):
            col = (95, 95, 108)
        else:
            col = (68, 68, 80)
        pygame.draw.rect(screen, col, self.rect, border_radius=6)
        txt = font.render(self.label, True, (240, 240, 240))
        screen.blit(txt, txt.get_rect(center=self.rect.center))


class Game:
    def __init__(self):
        pygame.init()
        pygame.display.set_caption("Chess vs AI")
        self.screen = pygame.display.set_mode((WIN_W, WIN_H))
        self.clock = pygame.time.Clock()
        self.font_s = pygame.font.SysFont("segoeui,arial,helvetica,dejavusans", 15)
        self.font = pygame.font.SysFont("segoeui,arial,helvetica,dejavusans", 18)
        self.font_b = pygame.font.SysFont("segoeui,arial,helvetica,dejavusans", 28, bold=True)
        self.pieces = build_piece_surfaces()

        self.hl_last = pygame.Surface((SQ, SQ), pygame.SRCALPHA)
        self.hl_last.fill((246, 246, 105, 130))
        self.hl_sel = pygame.Surface((SQ, SQ), pygame.SRCALPHA)
        self.hl_sel.fill((106, 190, 90, 150))
        self.hl_check = pygame.Surface((SQ, SQ), pygame.SRCALPHA)
        pygame.draw.circle(self.hl_check, (230, 40, 40, 170), (SQ // 2, SQ // 2), SQ // 2 - 2)
        self.dot = pygame.Surface((SQ, SQ), pygame.SRCALPHA)
        pygame.draw.circle(self.dot, (30, 30, 30, 90), (SQ // 2, SQ // 2), 12)
        self.ring = pygame.Surface((SQ, SQ), pygame.SRCALPHA)
        pygame.draw.circle(self.ring, (30, 30, 30, 90), (SQ // 2, SQ // 2), SQ // 2 - 3, 6)

        self.human = 'w'
        self.flip = False
        self.level = 'Medium'
        self.ai_stop = None
        self.ai_result = None
        self.token = 0
        self.thinking = False
        self.think_start = 0.0
        self.make_buttons()
        self.new_game()

    # ---- UI setup ----------------------------------------------------------
    def make_buttons(self):
        x = BOARD + 20
        self.buttons = [
            Button((x, 100, 105, 34), "New Game", self.new_game),
            Button((x + 115, 100, 105, 34), "Undo", self.undo),
            Button((x, 142, 105, 34), "Flip Board", self.toggle_flip),
            Button((x, 220, 105, 34), "White", lambda: self.set_side('w'), lambda: self.human == 'w'),
            Button((x + 115, 220, 105, 34), "Black", lambda: self.set_side('b'), lambda: self.human == 'b'),
            Button((x, 295, 68, 34), "Easy", lambda: self.set_level('Easy'), lambda: self.level == 'Easy'),
            Button((x + 76, 295, 68, 34), "Medium", lambda: self.set_level('Medium'), lambda: self.level == 'Medium'),
            Button((x + 152, 295, 68, 34), "Hard", lambda: self.set_level('Hard'), lambda: self.level == 'Hard'),
        ]

    # ---- game control --------------------------------------------------------
    def cancel_ai(self):
        if self.ai_stop is not None:
            self.ai_stop.set()
        self.token += 1
        self.thinking = False
        self.ai_result = None

    def new_game(self):
        self.cancel_ai()
        self.pos = Position()
        self.sans = []
        self.keys = [self.pos.key()]
        self.last_move = None
        self.selected = None
        self.promo_pending = None
        self.refresh()

    def set_side(self, side):
        self.human = side
        self.flip = (side == 'b')
        self.new_game()

    def set_level(self, level):
        self.level = level

    def toggle_flip(self):
        self.flip = not self.flip

    def refresh(self):
        pos = self.pos
        self.legal = pos.legal_moves()
        self.result = None
        if not self.legal:
            if pos.in_check(pos.turn):
                winner = 'White' if pos.turn == 'b' else 'Black'
                self.result = f"Checkmate! {winner} wins"
            else:
                self.result = "Stalemate - draw"
        elif insufficient_material(pos):
            self.result = "Draw - insufficient material"
        elif pos.halfmove >= 100:
            self.result = "Draw - 50-move rule"
        elif self.keys.count(self.keys[-1]) >= 3:
            self.result = "Draw - threefold repetition"
        self.selected = None

    def play_move(self, m):
        san = to_san(self.pos, m, self.legal)
        self.pos.make(m)
        self.sans.append(san)
        self.keys.append(self.pos.key())
        self.last_move = (m[0], m[1], m[2], m[3])
        self.refresh()

    def undo(self):
        self.cancel_ai()
        pos = self.pos
        undone_human = False
        while pos.stack:
            mover = pos.stack[-1][1][0]
            pos.unmake()
            self.sans.pop()
            self.keys.pop()
            if mover == self.human:
                undone_human = True
            if pos.turn == self.human and undone_human:
                break
        self.promo_pending = None
        if pos.stack:
            mv = pos.stack[-1][0]
            self.last_move = (mv[0], mv[1], mv[2], mv[3])
        else:
            self.last_move = None
        self.refresh()

    # ---- AI -----------------------------------------------------------------
    def book_move(self):
        n = len(self.pos.stack)
        if n == 0:
            cand = BOOK_FIRST
        elif n == 1:
            cand = BOOK_REPLY.get(coord(self.pos.stack[0][0]), [])
        else:
            return None
        cand = list(cand)
        random.shuffle(cand)
        for c in cand:
            for m in self.legal:
                if m[4] is None and coord(m) == c:
                    return m
        return None

    def start_ai(self):
        token = self.token
        stop = threading.Event()
        self.ai_stop = stop
        self.thinking = True
        self.think_start = time.time()
        pos_copy = self.pos.copy()
        cfg = LEVELS[self.level]
        book = self.book_move()

        def work():
            mv = book
            if mv is None:
                mv = Searcher(pos_copy, cfg['depth'], cfg['time'], cfg['noise'], stop).best_move()
            else:
                time.sleep(0.4)
            if not stop.is_set():
                self.ai_result = (token, mv)

        threading.Thread(target=work, daemon=True).start()

    def update_ai(self):
        if self.ai_result is not None:
            token, mv = self.ai_result
            self.ai_result = None
            if token == self.token and mv is not None:
                self.thinking = False
                self.play_move(mv)
                return
        if (not self.result and not self.thinking and not self.promo_pending
                and self.pos.turn != self.human):
            self.start_ai()

    # ---- input ---------------------------------------------------------------
    def sq_to_xy(self, r, c):
        if self.flip:
            return (7 - c) * SQ, (7 - r) * SQ
        return c * SQ, r * SQ

    def xy_to_sq(self, x, y):
        col, row = x // SQ, y // SQ
        if self.flip:
            return 7 - row, 7 - col
        return row, col

    def on_click(self, pos_xy):
        x, y = pos_xy
        for b in self.buttons:
            if b.rect.collidepoint(pos_xy):
                b.action()
                return
        if x >= BOARD:
            return
        if self.promo_pending:
            self.click_promo(x, y)
            return
        if self.result or self.thinking or self.pos.turn != self.human:
            return
        r, c = self.xy_to_sq(x, y)
        if self.selected:
            moves = [m for m in self.legal if (m[0], m[1]) == self.selected and (m[2], m[3]) == (r, c)]
            if moves:
                if moves[0][4] is not None:
                    self.promo_pending = (moves[0][0], moves[0][1], moves[0][2], moves[0][3])
                else:
                    self.play_move(moves[0])
                self.selected = None
                return
        p = self.pos.board[r][c]
        if p != '.' and p[0] == self.human:
            self.selected = (r, c)
        else:
            self.selected = None

    def promo_rect(self):
        return pygame.Rect((BOARD - 4 * SQ) // 2, (BOARD - SQ) // 2, 4 * SQ, SQ)

    def click_promo(self, x, y):
        rect = self.promo_rect()
        if rect.collidepoint(x, y):
            idx = (x - rect.x) // SQ
            fr, fc, tr, tc = self.promo_pending
            self.promo_pending = None
            self.play_move((fr, fc, tr, tc, 'QRBN'[idx]))
        else:
            self.promo_pending = None

    # ---- drawing -------------------------------------------------------------
    def draw_board(self):
        s = self.screen
        pos = self.pos
        for r in range(8):
            for c in range(8):
                x, y = self.sq_to_xy(r, c)
                pygame.draw.rect(s, LIGHT if (r + c) % 2 == 0 else DARK, (x, y, SQ, SQ))
        if self.last_move:
            for (r, c) in ((self.last_move[0], self.last_move[1]), (self.last_move[2], self.last_move[3])):
                s.blit(self.hl_last, self.sq_to_xy(r, c))
        if self.selected:
            s.blit(self.hl_sel, self.sq_to_xy(*self.selected))
        if not self.result or 'Checkmate' in (self.result or ''):
            for color in 'wb':
                if pos.in_check(color):
                    s.blit(self.hl_check, self.sq_to_xy(*pos.king[color]))
        # coordinates
        for i in range(8):
            file_i = 7 - i if self.flip else i
            rank_n = i + 1 if self.flip else 8 - i
            col_f = DARK if (7 + i) % 2 == 0 else LIGHT
            col_r = DARK if (i + 0) % 2 == 0 else LIGHT
            f_txt = self.font_s.render(FILES[file_i], True, col_f)
            s.blit(f_txt, (i * SQ + SQ - 12, BOARD - 18))
            r_txt = self.font_s.render(str(rank_n), True, col_r)
            s.blit(r_txt, (4, i * SQ + 3))
        # pieces
        for r in range(8):
            for c in range(8):
                p = pos.board[r][c]
                if p != '.':
                    s.blit(self.pieces[p], self.sq_to_xy(r, c))
        # legal move hints
        if self.selected:
            for m in self.legal:
                if (m[0], m[1]) == self.selected:
                    target = pos.board[m[2]][m[3]]
                    is_cap = target != '.' or (pos.board[m[0]][m[1]][1] == 'P' and m[1] != m[3])
                    s.blit(self.ring if is_cap else self.dot, self.sq_to_xy(m[2], m[3]))

    def draw_promo(self):
        rect = self.promo_rect()
        shade = pygame.Surface((BOARD, BOARD), pygame.SRCALPHA)
        shade.fill((0, 0, 0, 120))
        self.screen.blit(shade, (0, 0))
        pygame.draw.rect(self.screen, (235, 235, 235), rect.inflate(16, 16), border_radius=10)
        pygame.draw.rect(self.screen, (60, 60, 60), rect.inflate(16, 16), 3, border_radius=10)
        for i, t in enumerate('QRBN'):
            x = rect.x + i * SQ
            pygame.draw.rect(self.screen, LIGHT if i % 2 == 0 else DARK, (x, rect.y, SQ, SQ))
            self.screen.blit(self.pieces[self.human + t], (x, rect.y))

    def draw_wrapped(self, text, x, y, maxw, font, color):
        words, line = text.split(' '), ''
        for w in words:
            test = (line + ' ' + w).strip()
            if font.size(test)[0] > maxw and line:
                self.screen.blit(font.render(line, True, color), (x, y))
                y += font.get_linesize()
                line = w
            else:
                line = test
        self.screen.blit(font.render(line, True, color), (x, y))
        return y + font.get_linesize()

    def draw_panel(self):
        s = self.screen
        x = BOARD + 20
        pygame.draw.rect(s, (38, 38, 44), (BOARD, 0, PANEL, WIN_H))
        s.blit(self.font_b.render("Chess vs AI", True, (240, 240, 240)), (x, 14))

        if self.result:
            status, color = self.result, (255, 214, 102)
        elif self.thinking:
            dots = '.' * (int((time.time() - self.think_start) * 3) % 4)
            status, color = "AI is thinking" + dots, (150, 200, 255)
        else:
            who = 'White' if self.pos.turn == 'w' else 'Black'
            status = f"Your move ({who})"
            if self.pos.in_check(self.pos.turn):
                status += " - CHECK!"
            color = (230, 230, 230)
        self.draw_wrapped(status, x, 58, PANEL - 40, self.font, color)

        mouse = pygame.mouse.get_pos()
        for b in self.buttons:
            b.draw(s, self.font, mouse)
        s.blit(self.font.render("Play as", True, (170, 170, 180)), (x, 195))
        s.blit(self.font.render("Difficulty", True, (170, 170, 180)), (x, 270))
        s.blit(self.font.render("Moves", True, (170, 170, 180)), (x, 350))

        lines = []
        for i in range(0, len(self.sans), 2):
            w = self.sans[i]
            bl = self.sans[i + 1] if i + 1 < len(self.sans) else ''
            lines.append(f"{i // 2 + 1:>2}. {w:<8} {bl}")
        y = 374
        for ln in lines[-12:]:
            s.blit(self.font.render(ln, True, (215, 215, 220)), (x, y))
            y += 20

    def draw_game_over(self):
        banner = pygame.Surface((BOARD, 110), pygame.SRCALPHA)
        banner.fill((0, 0, 0, 175))
        self.screen.blit(banner, (0, BOARD // 2 - 55))
        t1 = self.font_b.render(self.result, True, (255, 255, 255))
        t2 = self.font.render("Press N or click New Game to play again", True, (210, 210, 210))
        self.screen.blit(t1, t1.get_rect(center=(BOARD // 2, BOARD // 2 - 12)))
        self.screen.blit(t2, t2.get_rect(center=(BOARD // 2, BOARD // 2 + 24)))

    def draw(self):
        self.draw_board()
        if self.promo_pending:
            self.draw_promo()
        if self.result:
            self.draw_game_over()
        self.draw_panel()
        pygame.display.flip()

    # ---- main loop -----------------------------------------------------------
    def run(self):
        while True:
            for e in pygame.event.get():
                if e.type == pygame.QUIT:
                    self.cancel_ai()
                    pygame.quit()
                    sys.exit()
                elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
                    self.on_click(e.pos)
                elif e.type == pygame.KEYDOWN:
                    if e.key == pygame.K_n:
                        self.new_game()
                    elif e.key == pygame.K_u:
                        self.undo()
                    elif e.key == pygame.K_f:
                        self.toggle_flip()
                    elif e.key == pygame.K_ESCAPE:
                        self.cancel_ai()
                        pygame.quit()
                        sys.exit()
            self.update_ai()
            self.draw()
            self.clock.tick(30)


def main():
    Game().run()


if __name__ == "__main__":
    main()