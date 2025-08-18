# LeanblueprintTesting

## Blueprint Guide
```
% Example: How to create section header
\section{Green's preorders (from \texttt{MyProject/GreensRelations.lean})}

% Example: How to write a definition (no dependencies)
\begin{definition}[Green's \(R\)-preorder]
  % Regesters the LaTeX label
  \label{def:RRel}
  Let \(M\) be a monoid and \(x,y\in M\).
  We define \(x \le_R y\) iff there exists \(z\in M\) with \(x\cdot z = y\).
  This relation is reflexive and transitive.
  % Lists the lean declarations (with namespaces) corrosponding to the surrounding definition
  \lean{RRel}
  % Claims the surrounding environment is fully formalized.
  \leanok
\end{definition}

% Example: How to write a theorem/lemma (with dependencies)
\begin{lemma}[Reflexivity of \(\le_R\)]
  \label{lem:RRel-refl}
  For every \(x\in M\), \(x \le_R x\).
  % Lists the lean declarations of the STATMENT 
  \lean{RRel.refl}
  % Claims that the STATMENT is formalized in lean (not necessarily proven)
  \leanok
  % Lists latex labels that are used to create the dependency graph.
  % This should list the depencencies of the STATEMENT (not proof)
  \uses{def:RRel}
\end{lemma}
% Optionally, include the following section to add a proof
\begin{proof}
  % Claims the proof is formalized in LEAN
  \leanok
  % Lists the dependencies of the PROOF
  % \uses{thm:example, lem:example2}
  Put proof description here.
\end{proof}

%TODO: test dfn vs lem vs prov vs thm vs cor
  % test \notready (claims the currounding environment is not ready to be formalized, needs blueprint work)
```