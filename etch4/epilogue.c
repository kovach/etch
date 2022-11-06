// sic

done();

auto t2 = std::chrono::high_resolution_clock::now();
std::cout << "took:" << std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count() << "μ" << std::endl;
std::cout << "took:" << std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count() << "ms" << std::endl;

std::cout << out << std::endl;
std::cout << fout << std::endl;
return 0;
}
