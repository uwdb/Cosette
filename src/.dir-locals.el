((coq-mode . ((eval . (progn
                        (setq coq-prog-name "/usr/local/bin/hoqtop")
                        (set (make-local-variable 'coq-prog-args)
                           (list "-emacs-U" "-R"
                           	 (replace-regexp-in-string "^/docker:[^:]+:" ""
                               (expand-file-name
                                 "./.build"
                                   (file-name-directory
                                     (let ((d (dir-locals-find-file ".")))
                                       (if (stringp d) d (car d))))))
                             "DopCert")))))))
          
