\documentclass[serif,mathserif,professionalfont,10pt]{beamer}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{etex}
\usepackage{graphicx}
\usepackage{textgreek}

\usepackage{agda}
\usepackage{amssymb}

\usepackage{color}
\definecolor{grey}{gray}{0.6}

\beamertemplatenavigationsymbolsempty
\usetheme{Boadilla}
\usecolortheme{beaver}

\makeatletter
\def\mkcommand#1{\expandafter\gdef\csname #1\endcsname}
\makeatother

\def\module#1{\message{#1}\section{#1}\sectlabel{#1}}

\newenvironment{ModuleHead}{\par\begingroup\tiny}{\endgroup\par\medskip}

\DeclareUnicodeCharacter{7472}{\ensuremath{^\mathsf{D}}} % MODIFIER LETTER CAPITAL D
\DeclareUnicodeCharacter{9723}{\ensuremath{\square}} % WHITE MEDIUM SQUARE
\DeclareUnicodeCharacter{119920}{\ensuremath{\mathbf{I}}} % MATHEMATICAL BOLD ITALIC CAPITAL I
\DeclareUnicodeCharacter{119991}{\ensuremath{_\mathsf{B}}} % MATHEMATICAL SCRIPT SMALL B
\DeclareUnicodeCharacter{120008}{\ensuremath{_\mathsf{S}}} % MATHEMATICAL SCRIPT SMALL S
\DeclareUnicodeCharacter{120001}{\ensuremath{_\mathsf{L}}} % MATHEMATICAL SCRIPT SMALL L
\DeclareUnicodeCharacter{119997}{\ensuremath{_\mathsf{H}}} % MATHEMATICAL SCRIPT SMALL H
\DeclareUnicodeCharacter{8348}{\ensuremath{_\mathsf{t}}} % MATHEMATICAL SCRIPT SMALL T
\DeclareUnicodeCharacter{8339}{\ensuremath{_\mathsf{x}}} % MATHEMATICAL SCRIPT SMALL X
\DeclareUnicodeCharacter{119925}{\ensuremath{\mathcal{N}}} % MATHEMATICAL BOLD ITALIC CAPITAL N
\DeclareUnicodeCharacter{119924}{\ensuremath{\mathcal{M}}} % MATHEMATICAL BOLD ITALIC CAPITAL M
\DeclareUnicodeCharacter{7484}{\ensuremath{\mathsf{O}}} % MODIFIER LETTER CAPITAL O
\DeclareUnicodeCharacter{9678}{\ensuremath{\mathsf{BULLSEYE}}} % BULLSEYE
\DeclareUnicodeCharacter{8667}{\ensuremath{\Rrightarrow}} % rightwards triple arrow
\DeclareUnicodeCharacter{8255}{\ensuremath{\smile}} % undertie, subscript-converse
\DeclareUnicodeCharacter{8265}{\ensuremath{! \! ? }} % exclamation question mark
\DeclareUnicodeCharacter{9632}{\ensuremath{ \square }} % black square
\DeclareUnicodeCharacter{9679}{\ensuremath{ \boldsymbol{\cdot} }} % black circle
\DeclareUnicodeCharacter{9675}{\ensuremath{ \boldsymbol{\circ} }} % white circle

\title{A tale of theories and data-structures}
\author[Carette, Al-hassy, Kahl]{Jacques Carette, Musa Al-hassy, Wolfram Kahl}
\institute[McMaster]{McMaster University, Hamilton}

\begin{document}

\frame{\titlepage}

% Start to fill the slides with verbiage that needs to evolve into something
% slide-like, with few words and many illustrations. But the words embody the
% plan and, to a certain extent, the verbal delivery of parts of the story.
\begin{frame}
\frametitle{Lists and Monoids}
Lists and Monoids are pervasive in functional programming.
They are related. A |List| is really a |Free Monoid|. What does that really mean?
Can it be explained more simply? One explanation is that |List| (with its |map| and
|fold| operations) is the \emph{language of monoids}. In other words, |List| is the
canonical term syntax for ``computing with monoids''.
\end{frame}

\AgdaHide{
\begin{code}
module _ where
open import Level
open import Structures.Monoid hiding (Forget; Forget-alg)
open import Function2 using (_$ᵢ)
open import Forget

open import Categories.Functor    using (Functor)
open import Categories.Adjunction using (Adjunction)
open import Categories.Agda       using (Sets)
open import Categories.Category using (Category)
\end{code}
}
\begin{frame}
\frametitle{A formal relation}
The free monoid functor is ``the'' left adjoint to the forgetful functor from
the category (monoids, homomorphisms) to the category (types, functions). Not Set.

Why on earth would we care about that? Let's see.

% Go to Agda code.  Show definitions of
% Monoid. Monoid Homomorphism. Forgetful functor.
% Then definition of Free and the Adjunction.
\end{frame}

\begin{frame}
\frametitle{Non-categorical version}
The requirements roughly translate to\\
Monoid:
\begin{itemize}
\item Need a \emph{container} C of α
\item with a distinguished container ε devoid of α's
\item a binary operation * that puts two containers together
\item such that ε is a left/right unit for *
\end{itemize}
Functor:
\begin{itemize}
\item a way to apply a (α → β) function to a C α to get a C β
\item which plays well with id, ∘, ≡ and *
\end{itemize}
Adjunction:
\begin{itemize}
\item singleton
\item foldr (over arbitrary Monoid)
\item foldr and singleton play well with each other
\end{itemize}
Bonus:
\begin{itemize}
\item Induction principle
\end{itemize}
\end{frame}
\end{document}