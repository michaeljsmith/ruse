set ts=2 sw=2 lisp ai

map <F5> :rightb vnew<CR>:setlocal buftype=nofile bufhidden=delete noswapfile<CR>:r! mzscheme -l errortrace -u src/ruse-bootstrap.ss test/test.ruse<CR>

