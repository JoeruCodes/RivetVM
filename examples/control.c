
int main() {
    int sum = 0;
    for (int i = 0; i < 10; ++i) {
        if (i & 1) {
            
            sum += i;
        }
        sum += i;
    }
    return sum; 
} 