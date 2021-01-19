Literate markdown
-----------------

The ideas about using '.lagda.md' files comes from Jesper Cockx blog post here:

https://jesper.sikanda.be/posts/literate-agda.html

You can add the following line to your '.emacs' to load the agda-mode for '.lagda.md' files:

(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))