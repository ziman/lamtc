% First of all, check against known constants
infer(Calculus, FunctionName, [], _ ⊢ FunctionType) :- decl(Calculus, FunctionName, FunctionType).

% λ→Curry

infer('λ→Curry', 'start rule',
	[],
	Gamma ⊢ A : Tau
) :- (A : Tau) ∊ Gamma.

infer('λ→Curry', '→ elimination', [
	Gamma ⊢ A : Tau → Sigma,
	Gamma ⊢ B : Tau],
	Gamma ⊢ A..B : Sigma
).

infer('λ→Curry', '→ introduction', [
	[A:Tau | Gamma] ⊢ B : Sigma],
	Gamma ⊢ A ⇒ B : Tau → Sigma
).

% λ→Church

infer('λ→Church', 'start rule',
	[],
	Gamma ⊢ A : Tau
) :- (A : Tau) ∊ Gamma.

infer('λ→Church', '→ elimination', [
	Gamma ⊢ A : Tau → Sigma,
	Gamma ⊢ B : Tau],
	Gamma ⊢ A..B : Sigma
).

infer('λ→Church', '→ introduction', [
	[A:Tau | Gamma] ⊢ B : Sigma],
	Gamma ⊢ (A : Tau) ⇒ B : Tau → Sigma
).

% λ2-Curry

infer('λ2-Curry', RuleName, Prerequisites, Rule) :-
	infer('λ→Curry', RuleName, Prerequisites, Rule).

infer('λ2-Curry', '∀-introduction',
	[ Gamma ⊢ M : Sigma ],
	Gamma ⊢ M : (forall(Alpha,Sigma))
) :- not(compound(Alpha)); not((Alpha : _) ∊ Gamma).

infer('λ2-Curry', '∀-elimination',
	[ Gamma ⊢ M : forall(Alpha, Sigma) ],
	Gamma ⊢ M : Sigma2
) :- not(compound(Alpha)); subst(Sigma, Alpha, _, Sigma2).

% λμ (incomplete)

infer('λμ', RuleName, Prerequisites, Rule) :-
	infer('λ→Curry', RuleName, Prerequisites, Rule).

infer('λμ', 'type equivalence',
	[ Gamma ⊢ M : Sigma, Sigma ~ Tau ],
	Gamma ⊢ M : Tau
).

% Functions

decl(_, 'zero',	zero : nat).
decl(_, 'succ',	succ : nat → nat).
decl('λ2-Curry', 'fix',	fix : forall(a, (a → a) → a)).
decl('λ2-Curry', 'id2',	id2 : forall(a, a → a)).
/*
decl(_, 'id', id : A → A).
decl(_, 'const', const : A → _ → A).
decl(_, 'ap', ap : (A → B → C) → (A → B) → A → C).
*/

% Utils

subst(Var, Var, Val, Val).
subst(X..Y, Var, Val, A..B) :-
	subst(X, Var, Val, A),
	subst(Y, Var, Val, B).
subst(X → Y, Var, Val, A → B) :-
	subst(X, Var, Val, A),
	subst(Y, Var, Val, B).
subst(Var ⇒ X, Var, _, Var ⇒ X).
subst(X ⇒ Y, Var, Val, A ⇒ B) :-
	X \= Var,
	subst(X, Var, Val, A),
	subst(Y, Var, Val, B).
subst(forall(Var, X), Var, _, forall(Var, X)).
subst(forall(X,Y), Var, Val, forall(A,B)) :-
	X \= Var,
	subst(X, Var, Val, A),
	subst(Y, Var, Val, B).

not_in(_, []).
not_in(X, [Y|Ys]) :- X \= Y, not_in(X, Ys).

∊(A, [A|_]).
∊(A, [X|Xs]) :- A \= X, A ∊ Xs.
