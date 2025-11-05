# aps-matematica-discreta-prolog

Para rodar:

Instale o interpretador do Prolog neste site:

    https://www.swi-prolog.org/download/stable

Depois de instalar (e reiniciar o VSCode), rode o comando:

    swipl

no terminal. Se tudo estiver certo, deverá aparecer:

    Welcome to SWI-Prolog (threaded, 64 bits, version 9.2.9)
    SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software.
    Please run ?- license. for legal details.

    For online help and background, visit https://www.swi-prolog.org
    For built-in help, use ?- help(Topic). or ?- apropos(Word).

    1 ?-

Insira no terminal [undertale]. (ficará `1 ?- [undertale].`), deve retornar `true.`.

-----------------------------------------------------------------------------------------------------------------
## APS — Lógica e Matemática Discreta
### Giovanna Barros Scalco e Gustavo Nicácio

**Objetivo**
Aplicar os conceitos de Lógica de Primeira Ordem para representar formalmente o universo do jogo Undertale, utilizando predicados, funções e quantificadores. Em seguida, demonstrar deduções naturais com base nas regras lógicas e, depois, implementar o modelo em Prolog.

**Cenário Escolhido: Undertale**
No universo de Undertale, humanos e monstros coexistem em um mundo em que as ações dos personagens determinam diferentes rotas narrativas: Pacifista, Neutra e Genocida, em que depende do número de monstros que o personagem decide enfrentar. Para esta atividade pode-se modelar logicamente as relações entre personagens.

### Modelagem Lógica
**Predicado**
H(x) - x é humano
M(x) - x é monstro
D(x) - x tem determinação
P(x) - x está trilhando a rota pacifista
N(x) - x está trilhando a rota neutra
G(x) - x está trilhando a rota genocida

**Relação**
C(x,y) - x é pai/mãe de y
K(x,y) - x matou y
S(x,y) - x poupou y
F(x,y) - x é amigo de y

**Constante**
f - Flowey
s - Sans
t - Toriel

### Fórmulas em Lógica de Primeira Ordem
∀x( H(x) ∧ ∀y( M(y) ∧ K(x, y) ) ∧ ¬∃z( M(z) ∧ S(x, z) ) → G(x) )
∀x( H(x) ∧ ∃yS(x, y) → P(x) ∨ N(x) )
∀x( H(x) ∧ ∃yK(x, y) → G(x) ∨ N(x) )
∀x( H(x) ∧ ∃yK(x, y) ∧ ∃zS(x, z) → N(x) )
∀x( D(x) → H(x) ∨ M(x) ∨ x = f )
∀x( H(x) ∧ G(x) ∧ S(x, s) → K(s, x) )
∀x( (H(x) ∧ ¬M(x)) ∨ (¬H(x) ∧ M(x)) )
∀x∀y∃z( (C(x, y) ∧ K(z, y)) → ¬F(x, z) )
∀x∀y( H(x) ∧ M(y) ∧ P(x) → F(y, x) )
∃x( M(x) ∧ ∀y( H(y) ∧ S(x, y) ) → x = t )

**Dedução Natural**
*Para o caso 7:*
∀x( (H(x) ∧ ¬M(x)) ∨ (¬H(x) ∧ M(x)) ) deve chegar em ∀xH(x) -> ∀x(¬M(x))


*Para o caso 8:*
∀x∀y∃z((C(x,y)∧K(z,y))→¬F(x,z))


### Implementação em Prolog

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
  spared(X, S).

%%%% FÓRMULA 7
% ∀x( (H(x) ∧ ¬M(x)) ∨ (¬H(x) ∧ M(x)) )
integrity_human_not_monster(X) :- human(X), \+ monster(X).
integrity_monster_not_human(X) :- monster(X), \+ human(X).

%%%% FÓRMULA 8
% ∀x∀y∃z( C(x,y) ∧ K(z,y) → ¬F(x,z) )
not_friend(X, Z) :- parent(X, Y), killed(Z, Y).
not_friend(Z, X) :- parent(X, Y), killed(Z, Y).

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

O programa foi estruturado em quatro partes principais:
Constantes e fatos: definem humanos, monstros, relações familiares e ações do jogo;
Predicados auxiliares: funções para checar condições, como monstros mortos ou poupados;
Fórmulas previamente definidas: traduções das proposições lógicas apresentadas na APS para a sintaxe de Prolog.
Consultas: exemplos de execução para verificar os comportamentos esperados.
A modelagem segue a lógica proposta, permitindo testar rotas definidas como genocida, neutra ou pacifista
Consultas e resultados esperados
% ?- route(frisk, R).                  → R = neutral.
% ?- integrity_human_not_monster(frisk). → true.
% ?- not_friend(toriel, frisk).       → false.
% ?- friend(papyrus, frisk).          → false.
% ?- is_toriel(toriel).               → true

- Frisk segue a rota neutra (matou e poupou monstros);
- Humanos e monstros mantém integridade de tipo;
- Toriel não é inimiga de Frisk e poupa todos os humanos;
- O comportamento geral está de acordo com as fórmulas lógicas definidas.

Portanto, o modelo Prolog desenvolvido cumpre o objetivo de representar logicamente as relações e ações do universo Undertale, demonstrando como a lógica de predicados pode ser aplicada para simular cenários narrativos e verificar formalmente propriedades definidas por fórmulas matemáticas.
