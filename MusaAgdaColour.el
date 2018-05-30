;; Agda Colouring of Multiple Files --- Musa Al-hassy
;;
;; Agda has a weak latex back-end that can colour a single lagda file,
;; but has no colour support for including files.
;;
;; We cannot merely use \include{} and run the latex backend
;; as the colours are only known after typechecking and so the file
;; would be typechecked first. This would crash since there would then
;; be multiple top-level modules which is not how modules are intended to work:
;; One top-level module per file.
;;
;; Instead I colour code each ``included'' file, then latex \include{} the resulting
;; coloured latex into the main latex file.
;;
;;
;; WARNING: JC & WK please do not use anything from here directly.
;;          It's all extremely fragile. For now, In report.org, simply execute
;;          (colour-and-preview "Structures/X.tex") to ensure that X has no latex errors
;;          then #+INCLUDE it and then execute the provided compile command to get things working.
;;
;;          Do not abort (colour ...) as it is working, otherwise, will need to make manual changes.
;; 
;;
;; Issues.
;; 0. Make copies of altered files so that if commands are aborted then no manual changes need to happen.
;;      Delete such intermediary working copies after execution.
;; 1. Latex Administrivia is currently hard coded; instead it ought to be exported from the main document.
;;      Possibly delimited via some tokens, then for deletion we consider the length.
;;      Possibly easier is to make a `header.ltx` file and then `input` it into the files; also in the main file ;-)
;;
;; 2. In the intermediary files, replace |lhsformat| with \verb|lhsformat|, so that it latex goes through.
;; 3. Remove all lines beginning with a `%`; since the agda latex back-end keeps those for some reason?
;;      Of note are the folding markers %{{{ and %}}}, as well as the quick guide to folding mode.

(defun org-keywords ()
  "Parse the buffer and return a cons list of (property . value) from lines like: #+PROPERTY: value"
  (org-element-map (org-element-parse-buffer 'element) 'keyword
                   (lambda (keyword) (cons (org-element-property :key keyword)
                                           (org-element-property :value keyword)))))
;; Src: http://kitchingroup.cheme.cmu.edu/blog/2013/05/05/Getting-keyword-options-in-org-files/

(defun org-keyword (KEYWORD)
  "Get the value of a KEYWORD in the form of #+KEYWORD: value"
  (cdr (assoc KEYWORD (org-keywords)))
)

(defun org-keyword-values (KEYWORD)
  "Get *all* values of every ``#+KEYWORD: value'' pair."
  (mapcar 'cdr (remove-if-not (lambda (x) (equal (car x) KEYWORD)) (org-keywords)))
)

(defun within-file (FILE &rest fs)
  "Perform operations `fs` within a buffer contining contents of `FILE`."

  ;; disable all local vars  
  (setq enable-local-variables nil enable-local-eval nil)
  (find-file FILE)

  ;; Execute the given operations.
  ; (mapcar 'eval fs) ;; returns a list
  ;; executes each element without returning a list
  (dolist (f fs) (eval f) )

  ;; (kill-buffer)

  ;; re-enable safe local vars that necessitate querying user.
  (setq enable-local-variables t enable-local-eval t)
)

; Test:
;; '(within-file "Structures/TwoSorted.lagda"
;;   '(insert "Oh really\n")
;;   '(goto-line (point-min))
;;   ; '(sleep-for 3)
;;   '(kill-line)
;;   '(kill-line)
;;   '(save-buffer)
;; )

(defun insert-latex-adminstriva ()
  "Insert the necessary LaTeX \begin{document}…\end{document} to produce a standlone LaTeX file."
    
  ;; Insert header, and save location of where we stopped inserting.
  (goto-line (point-min))
  (insert "\\documentclass[11pt]{article}
  \\usepackage{agda}
  \\usepackage{RathAgdaChars}
  \\DeclareUnicodeCharacter{737}{\\ensuremath{737}}
  \\DeclareUnicodeCharacter{119922}{\ensuremath{119922}}
  \\begin{document}\n")
  (setq START (point))

  ;; Insert postmatter, and save location of where insertion began.
  (setq FINISH (point-max))
  (goto-line FINISH)
  (insert "\n\\end{document}")
)

(defun delete-latex-adminstriva ()
  "Delete the necessary LaTeX \begin{document}…\end{document} to obtain a file suitable for \include{⋯}."

  ;; Since the FINISH location was saved *after* some insertations occured,
  ;; it must be accessed before those particular insertations are removed!

  ;; Delete postmatter from saved location to end.
  (delete-region FINISH (point-max))

  ;; Delete header from start to saved location.
  (delete-region (point-min) START)
)

(defun colour (DirNameExt &optional preview)
  "Produce coloured agda for given `NAME.lagda`, where `DirNameExt=Directory/NAME.ext`.

   If the `preview` flag is true, then we move the resulting PDF to the directory of
   the parent file, the one containg the #+INCLUDE. Then open the PDF for a glance.
   This is nice for previewing ; debugging individual files.
  "
  (message (concat "Begun Colour Processing " DirNameExt)); E.g., = Structures/TwoSorted.tex
  (let* ( (DirNAME (file-name-sans-extension DirNameExt)) ;       = Structures/TwoSorted
          (NAME    (file-name-nondirectory DirNAME))      ;       = TwoSorted
	  (Dir     (file-name-directory    DirNAME))      ;       = Structures/

	  (DirNAMELagda     (concat DirNAME ".lagda"))
	  (InsertPostMatter (concat "echo \"\\end{document}\" >> " DirNAMELagda))
	  (DeletePostMatter (concat "sed -i '$ d' " DirNAMELagda))
	  (InsertPreMatter  (concat "sed -i '01i \\ \\\\documentclass[11pt]{article} \\
  \\\\usepackage{agda}                      \\
  \\\\usepackage{RathAgdaChars}             \\
  \\\\usepackage{verbatim}                   \\
  \\\\DeclareUnicodeCharacter{737}{\\\\ensuremath{737}} \\
  \\\\DeclareUnicodeCharacter{119922}{\\\\ensuremath{119922}} \\
  \\\\begin{document}' " DirNAMELagda))
         (DeletePreMatter (concat "sed -e '1,7d' -i " DirNAMELagda))
       )


    (shell-command (concat

         InsertPreMatter
     " ; " InsertPostMatter

     " ; " (concat "DirNAME=" DirNAME "; Dir=" Dir "; NAME=" NAME
         "; agda --latex $DirNAME.lagda "
          "&& cd latex && pdflatex $DirNAME.tex ")

   "; cd .."            
   " ; " DeletePreMatter
   " ; " DeletePostMatter

   "; cd latex "

   ;; Santize and relocate the agda coloured tex file
   "; mv " DirNAME ".tex ../" Dir
   (concat "; sed -i '$ d' ../" DirNAME ".tex") ;; delete postmatter
   (concat "; sed -e '1,7d' -i ../" DirNAME ".tex")    ;; delete prematter		   
   
   ; The resuling pdf is not in Dir but rather in latex/, so we move NAME.pdf rather than DirNAME.pdf.
   (if preview "&& mv $NAME.pdf ../$Dir && cd .. && (evince $DirNAME.pdf &)" "")

   ))

    ; '(setq enable-local-variables nil enable-local-eval nil)
    ; '(find-file DirNAMELagda)

 )
)

; Test: '(colour "Structures/TwoSorted.tex" 't)
; Test: '(colour "Structures/OneCat.tex" 't)

; 
; echo "\end{document}" >> del.txt
; 
; sed -i '01i\\documentclass[11pt]{article} \
;   \\usepackage{agda}                      \
;   \\usepackage{RathAgdaChars}             \
;   \\DeclareUnicodeCharacter{737}{\\ensuremath{737}} \
;   \\DeclareUnicodeCharacter{119922}{\\ensuremath{119922}} \
;   \\begin{document}' del.txt
; 
; sed -e '1,6d' -i del.txt
; 
; sed -i '$ d' del.txt

;; IGNORE: previous emacs-based attempt.
;; 
;;  (within-file (concat DirNAME ".lagda"))
;; ; disable all local vars  
;; setq enable-local-variables nil enable-local-eval nil)
;; find-file (concat DirNAME ".lagda"))
;; 
;;   ;; Insert preprocessing.
;;   (and (progn (insert-latex-adminstriva) (save-buffer) 1))
;;   (read-string "inserted!")
;; 
;;   ;; Colour
;;   (then        
;;   (shell-command (concat "DirNAME=" DirNAME "; Dir=" Dir "; NAME=" NAME
;;   "; cd ..; agda --latex $DirNAME.lagda "
;;   "&& cd latex && pdflatex $DirNAME.tex "
;; 
;;   ; The resuling pdf is not in Dir but rather in latex/, so we move NAME.pdf rather than DirNAME.pdf.
;;   (if preview "&& mv $NAME.pdf ../$Dir && cd .. && evince $DirNAME.pdf &" "")
;;   ))
;; 
;;   ;; Delete Preprocessing.
;;   ; (read-string "pause?")
;;   (progn (delete-latex-adminstriva) (message "deleted")
;;   (save-buffer) (kill-buffer) )
;;   )
;; 
;; setq enable-local-variables t enable-local-eval t)
;; 

(defun then (first second) "Force `first` to evaluate fully, then and only then do we do `second`!"
 ( (lambda (x) (eval second)) (eval first) ) 
)

;; '(then (message "first") (progn (message "second") (sleep-for 1)))

;; Test: '(colour "Structures/TwoSorted.tex" 't)
;; Test: '(colour-and-preview "Structures/OneCat.tex")
;; Test: '(colour "Structures/OneCat.tex" 't)

(defun colour-and-preview (DirNameExt)
  "Produce coloured agda for given `NAME.lagda`, where `DirNameExt=Directory/NAME.ext`.
   Then move the resulting PDF to the directory of the parent file, the one containg the #+INCLUDE.
   Finally open the PDF for a glance.

   Nice for previewing ; debugging individual files.
  "
  (colour DirNameExt 't)
)

(defun show (x) "A debugging function that inserts `x` as a string at the current location"
  (insert "\n" (format "%s" x))
)

(defun compose () "Colour and compose all includes to produce a full report."
  (interactive)

  (message (format "Agda: Composing article %s " (buffer-file-name)))
  (sleep-for 1)

  (message "Agda: Begun colouring #+INCLUDE's.") (sleep-for 1)
  (mapcar 'colour (org-keyword-values "INCLUDE"))

  (message "Agda: Begun processing “tads”.") (sleep-for 1)
  (org-latex-export-to-latex)
  ; (eshell-command (concat "mv tads.tex tads.lagda ;"
  ; ))
  (shell-command "mv tads.tex tads.lagda ; NAME=tads ; agda --latex $NAME.lagda ; cd latex ; pdflatex $NAME.tex ; mv $NAME.pdf .. ; cd .. ; evince $NAME.pdf &")
  ; (colour-and-preview "./tads.tex") ??? ToFix. Why doesn't this work? Oh, because of the inseration and removal of latex adminstriva.
)

(global-set-key (kbd "<f7>") 'compose)
