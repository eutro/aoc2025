((lean4-mode
  (eval . (unless (featurep 'aoc2025-eutro)
            (let ((load-path (cons (locate-dominating-file
                                    (or load-file-name (buffer-file-name))
                                    "aoc2025-eutro.el")
                                   load-path)))
              (require 'aoc2025-eutro))))
  (eval . (aoc2025-eutro-mode))))
