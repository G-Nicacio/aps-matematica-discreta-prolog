/*** ==========================================================
    UNDERTALE — APS LMD (Giovanna Scalco & Gustavo Nicacio)
==============================================================*/

:- discontiguous killed/2.

%%%% CONSTANTES
alias(f, flowey).
alias(s, sans).
alias(t, toriel).

%%%% FATOS

% Humanos
human(frisk).

% Monstros
monster(sans).
monster(papyrus).
monster(asgore).
monster(toriel).
monster(undyne).
monster(mettaton).
monster(flowey).

% Relações familiares
parent(toriel, frisk).     % Toriel é figura materna de Frisk
parent(asgore, frisk).     % Asgore é figura paterna de Frisk

% Determinação
determined(frisk).
determined(undyne).
determined(flowey).

% Ações
killed(frisk, undyne).
spared(frisk, papyrus).
spared(toriel, frisk).


%%%% HELPERS

exists_killed_monster(X) :- killed(X, Y), monster(Y).
exists_spared_monster(X) :- spared(X, Y), monster(Y).

% ∀y(M(y) ∧ K(x,y))
killed_all_monsters(X) :-
  \+ ( monster(Y), \+ killed(X, Y) ).

% ¬∃z(M(z) ∧ S(x,z))
spared_no_monster(X) :-
  \+ ( monster(Z), spared(X, Z) ).

% ∀y(H(y) ∧ S(x,y))
spares_all_humans_conj(X) :-
  \+ ( human(Y), \+ spared(X, Y) ).

%%%% FÓRMULAS (1-10)

%%%% FÓRMULA 1
% ∀x( H(x) ∧ ∀y( M(y) ∧ K(x,y) ) ∧ ¬∃z( M(z) ∧ S(x,z) ) → G(x) )
genocidal(X) :-
  human(X),
  killed_all_monsters(X),
  spared_no_monster(X).

%%%% FÓRMULA 2
% ∀x( H(x) ∧ ∃y S(x,y) → P(x) ∨ N(x) )
% (satisfeita indiretamente via definições de P e N)

%%%% FÓRMULA 3
% ∀x( H(x) ∧ ∃y K(x,y) → G(x) ∨ N(x) )
% (satisfeita indiretamente via definições de G e N)

%%%% FÓRMULA 4
% ∀x( H(x) ∧ ∃y K(x,y) ∧ ∃z S(x,z) → N(x) )
neutral(X) :-
  human(X),
  exists_killed_monster(X),
  exists_spared_monster(X).

%%%% REGRAS ÚTEIS
% Pacifista: não matou ninguém e poupou alguém
pacifist(X) :-
  human(X),
  \+ exists_killed_monster(X),
  exists_spared_monster(X).

%%%% FÓRMULA 5
% ∀x( D(x) → H(x) ∨ M(x) ∨ x = f )
determined_is_h_or_m_or_f(X) :-
  determined(X),
  ( human(X)
  ; monster(X)
  ; alias(f, X)
  ).

%%%% FÓRMULA 6
% ∀x( H(x) ∧ G(x) ∧ S(x, s) → K(s, x) )
killed(sans, X) :-
  human(X),
  genocidal(X),
  alias(s, S),
  spared(X, S).

%%%% FÓRMULA 7
% ∀x( (H(x) ∧ ¬M(x)) ∨ (¬H(x) ∧ M(x)) )
integrity_human_not_monster(X) :- human(X), \+ monster(X).
integrity_monster_not_human(X) :- monster(X), \+ human(X).

%%%% FÓRMULA 8
% ∀x∀y∃z( C(x,y) ∧ K(z,y) → ¬F(x,z) )
not_friend(X, Z) :-
  parent(X, Y),
  killed(Z, Y).

%%%% FÓRMULA 9
% ∀x∀y( H(x) ∧ M(y) ∧ P(x) → F(y,x) )
friend(Y, X) :-
  human(X),
  monster(Y),
  pacifist(X),
  \+ not_friend(Y, X).

%%%% FÓRMULA 10
% ∃x( ∀y( M(x) ∧ H(y) ∧ S(x, y) ) → x = t )
is_toriel(X) :-
  monster(X),
  spares_all_humans_conj(X),
  alias(t, X).


%%%% CONSULTAS DE EXEMPLO

% 1. Ver rota de Frisk (fórmulas 1–4)
% ?- route(frisk, R).
route(X, genocidal) :- genocidal(X).
route(X, pacifist)  :- pacifist(X).
route(X, neutral)   :- neutral(X).

% 2. Integridade de tipos (fórmula 7)
% ?- integrity_human_not_monster(frisk), integrity_monster_not_human(sans).

% 3. Relação de inimizade (fórmula 8)
% ?- not_friend(toriel, frisk).

% 4. Amizade (fórmula 9)
% ?- friend(papyrus, frisk).

% 5. Monstro que poupa todos os humanos (fórmula 10)
% ?- is_toriel(toriel).


%%%% RESULTADOS ESPERADOS PARA O CENÁRIO ATUAL

% ?- route(frisk, R).                  → R = neutral.
% ?- integrity_human_not_monster(frisk). → true.
% ?- not_friend(toriel, frisk).       → false.
% ?- friend(papyrus, frisk).          → false.
% ?- is_toriel(toriel).               → true.
