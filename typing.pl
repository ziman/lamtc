% Typechecker/typing prover.
%
% usage: proof(Calculus, Gamma ⊢ Term : Type).
%
% Gamma is a list of terms.
% Special syntax:
% 	f .. x	— function application
% 	x ⇒ f x — abstraction, equiv. (λx.fx)
%
% Examples:
%   proof('λ→Curry',  [] ⊢ f ⇒ x ⇒ f..(f..(f..x)) : (nat → nat) → nat → nat).
%   proof('λ→Church', [] ⊢ (f : nat → nat) ⇒ (x : nat) ⇒ f..(f..(f..x)) : (nat → nat) → nat → nat).
%   proof('λ2-Curry', [] ⊢ x ⇒ x..x : forall(b, forall(a, a) → b → b)).
%   proof('λ2-Curry', [] ⊢ x ⇒ y ⇒ x : forall(a, forall(b, a → b → a))).
%   proof('λ2-Curry', [] ⊢ x ⇒ x : forall(a, a → a)).
% http://ziman.functor.sk/proof.txt

% Logic operators

:- op(110, yfx, '⊢').
:- op(100, xfx, ':').
:- op(95, xfy, '~').
:- op(90, xfy, '→').
:- op(70, xfy, '⇒').
:- op(60, yfx, '∊').
:- op(50, yfx, '..').

%% λ-calculi

:- include(calculi).

% Proving mechanisms

proof(Calculus, X) :-
	prove(Calculus, X, Proof),
	format_steps(Proof).

prove(Calculus, X, Proof) :-
	prove_tree(Calculus, X, TreeProof),
	linearize(TreeProof, [], ProofR),
	reverse(ProofR, Proof),
	first_num(Proof, 1),
	bind_nums(Proof).

prove_tree(Calculus, X, Proof) :-
	infer(Calculus, RuleName, Ys, X),
	prove_tree_all(Calculus, Ys, Ts),
	Proof = step(_, X, RuleName, Ts).


prove_tree_all(_, [],  []).
prove_tree_all(Calculus, [X|Xs], [T|Ts]) :- prove_tree(Calculus, X, T), prove_tree_all(Calculus, Xs, Ts).

first_num([], _).
first_num([step(X,_,_,_)|_], X).

bind_nums([]).
bind_nums([step(_,_,_,_)]).
bind_nums([step(X,_,_,_),step(Y,Yt,R,Yd)|Zs]) :-
	Y is X + 1,
	bind_nums([step(Y,Yt,R,Yd)|Zs]).

linearize(step(Num, Term, RuleName, Deps), PrevSteps, [CurStep|Proof]) :-
	CurStep = step(Num, Term, RuleName, DepNums),
	linearize_each(Deps, PrevSteps, Proof, DepNums).

linearize_each([], PrevSteps, PrevSteps, []).
linearize_each([X|Xs], PrevSteps, Proof, [Num|Nums]) :-
	linearize_each(Xs, PrevSteps, InterProof, Nums),
	linearize(X, InterProof, Proof),
	first_num(Proof, Num).

format_steps([]) :- write('Q.E.D.\n').
format_steps([step(No, Term, RuleName, Deps)|Ys]) :-
	write(No), write('. '), write(Term), 
	(Deps = [],
		write('  ('), write(RuleName), write(')\n');
	 Deps \= [],
		write('  ('), write(Deps), write(', '), write(RuleName), write(')\n')
	),
	format_steps(Ys).
